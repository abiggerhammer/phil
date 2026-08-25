{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationDependency
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationAdmissionDecision (..)
  , QualificationAdmissionRevision (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-012 direct independent ground closes qualification" directGroundAccepted
    , test "PROV-012 grounded dependency chain closes transitively" groundedChainAccepted
    , test "PROV-012 ungrounded mutual cycle rejects" ungroundedCycleRejected
    , test "PROV-012 grounded mutual cycle closes conditionally" groundedCycleAccepted
    , test "PROV-012 ungrounded self-cycle rejects" selfCycleRejected
    , test "PROV-012 unknown admission dependency rejects" unknownAdmissionRejected
    , test "PROV-012 unknown ground dependency rejects" unknownGroundRejected
    , test "PROV-012 rejected independent ground rejects" rejectedGroundRejected
    , test "PROV-012 rejected dependency admission rejects" rejectedAdmissionRejected
    , test "PROV-012 unrelated rejected registry node is ignored" unrelatedRejectedNodeIgnored
    , test "PROV-012 transitive closure retains all independent grounds" multipleGroundsPropagate
    , test "PROV-012 registry ordering is nonsemantic" registryOrderingIsCanonical
    , test "PROV-012 unknown selected root rejects" unknownRootRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

directGroundAccepted :: Either String ()
directGroundAccepted = do
  checked <- mapLeft show $ checkProviderQualificationDependencyGraph $
    graph [nodeA Set.empty (Set.singleton proofGroundKey)] [proofGround] [admissionA]
  assert
    (Map.lookup admissionA (checkedQualificationDependencyGroundsByAdmission checked)
      == Just (Set.singleton proofGroundKey))
    "direct proof ground not retained"

groundedChainAccepted :: Either String ()
groundedChainAccepted = do
  let root = nodeA (Set.singleton admissionB) Set.empty
      dependency = nodeB Set.empty (Set.singleton runtimeGroundKey)
  checked <- mapLeft show $ checkProviderQualificationDependencyGraph $
    graph [root, dependency] [runtimeGround] [admissionA]
  assert
    (Map.lookup admissionA (checkedQualificationDependencyGroundsByAdmission checked)
      == Just (Set.singleton runtimeGroundKey))
    "root did not inherit dependency ground"

ungroundedCycleRejected :: Either String ()
ungroundedCycleRejected = do
  let a = nodeA (Set.singleton admissionB) Set.empty
      b = nodeB (Set.singleton admissionA) Set.empty
  case checkProviderQualificationDependencyGraph (graph [a, b] [] [admissionA]) of
    Left (QualificationDependencyUngrounded admissions) ->
      assert (admissions == Set.fromList [admissionA, admissionB])
        "ungrounded cycle diagnostic did not retain both admissions"
    other -> Left ("ungrounded cycle was accepted: " <> show other)

groundedCycleAccepted :: Either String ()
groundedCycleAccepted = do
  let a = nodeA (Set.singleton admissionB) (Set.singleton assumptionGroundKey)
      b = nodeB (Set.singleton admissionA) Set.empty
  checked <- mapLeft show $ checkProviderQualificationDependencyGraph $
    graph [a, b] [assumptionGround] [admissionA]
  let groundsByAdmission = checkedQualificationDependencyGroundsByAdmission checked
  assert
    (Map.lookup admissionA groundsByAdmission == Just (Set.singleton assumptionGroundKey)
      && Map.lookup admissionB groundsByAdmission == Just (Set.singleton assumptionGroundKey))
    "grounded SCC did not propagate its independent assumption"

selfCycleRejected :: Either String ()
selfCycleRejected = do
  let a = nodeA (Set.singleton admissionA) Set.empty
  case checkProviderQualificationDependencyGraph (graph [a] [] [admissionA]) of
    Left (QualificationDependencyUngrounded admissions) ->
      assert (admissions == Set.singleton admissionA) "wrong self-cycle diagnostic"
    other -> Left ("ungrounded self-cycle was accepted: " <> show other)

unknownAdmissionRejected :: Either String ()
unknownAdmissionRejected = do
  let unknown = QualificationAdmissionRevision "admission:missing"
      a = nodeA (Set.singleton unknown) (Set.singleton proofGroundKey)
  case checkProviderQualificationDependencyGraph (graph [a] [proofGround] [admissionA]) of
    Left (QualificationDependencyUnknownAdmission owner dependency) -> do
      assert (owner == admissionA) "wrong owner for missing admission"
      assert (dependency == unknown) "wrong missing admission"
    other -> Left ("unknown admission dependency was accepted: " <> show other)

unknownGroundRejected :: Either String ()
unknownGroundRejected = do
  let missingGround = QualificationGroundKey "ground:missing"
      a = nodeA Set.empty (Set.singleton missingGround)
  case checkProviderQualificationDependencyGraph (graph [a] [] [admissionA]) of
    Left (QualificationDependencyUnknownGround owner groundKey) -> do
      assert (owner == admissionA) "wrong owner for missing ground"
      assert (groundKey == missingGround) "wrong missing ground key"
    other -> Left ("unknown ground dependency was accepted: " <> show other)

rejectedGroundRejected :: Either String ()
rejectedGroundRejected = do
  let rejected = proofGround
        { qualificationGroundDisposition =
            QualificationGroundRejected (Set.singleton "proof-revoked") }
      a = nodeA Set.empty (Set.singleton proofGroundKey)
  case checkProviderQualificationDependencyGraph (graph [a] [rejected] [admissionA]) of
    Left (QualificationDependencyRejectedGround owner key reasons) -> do
      assert (owner == admissionA) "wrong owner for rejected ground"
      assert (key == proofGroundKey) "wrong rejected ground key"
      assert (reasons == Set.singleton "proof-revoked") "wrong rejection reasons"
    other -> Left ("rejected ground was accepted: " <> show other)

rejectedAdmissionRejected :: Either String ()
rejectedAdmissionRejected = do
  let a = nodeA (Set.singleton admissionB) (Set.singleton proofGroundKey)
      b = (nodeB Set.empty (Set.singleton runtimeGroundKey))
        { qualificationDependencyAdmissionDecision =
            QualificationRejected (Set.singleton "policy-rejected") }
  case checkProviderQualificationDependencyGraph
      (graph [a, b] [proofGround, runtimeGround] [admissionA]) of
    Left (QualificationDependencyRejectedAdmission revision reasons) -> do
      assert (revision == admissionB) "wrong rejected admission"
      assert (reasons == Set.singleton "policy-rejected") "wrong admission reasons"
    other -> Left ("rejected dependency admission was accepted: " <> show other)

unrelatedRejectedNodeIgnored :: Either String ()
unrelatedRejectedNodeIgnored = do
  let root = nodeA Set.empty (Set.singleton proofGroundKey)
      unrelated = (nodeB Set.empty Set.empty)
        { qualificationDependencyAdmissionDecision =
            QualificationRejected (Set.singleton "stale") }
  _ <- mapLeft show $ checkProviderQualificationDependencyGraph $
    graph [root, unrelated] [proofGround] [admissionA]
  Right ()

multipleGroundsPropagate :: Either String ()
multipleGroundsPropagate = do
  let c = nodeC Set.empty (Set.singleton externalGroundKey)
      b = nodeB (Set.singleton admissionC) (Set.singleton runtimeGroundKey)
      a = nodeA (Set.singleton admissionB) (Set.singleton proofGroundKey)
  checked <- mapLeft show $ checkProviderQualificationDependencyGraph $
    graph [a, b, c] [proofGround, runtimeGround, externalGround] [admissionA]
  assert
    (Map.lookup admissionA (checkedQualificationDependencyGroundsByAdmission checked)
      == Just (Set.fromList [proofGroundKey, runtimeGroundKey, externalGroundKey]))
    "transitive ground union was incomplete"

registryOrderingIsCanonical :: Either String ()
registryOrderingIsCanonical = do
  let a = nodeA (Set.fromList [admissionB, admissionC]) Set.empty
      b = nodeB Set.empty (Set.singleton proofGroundKey)
      c = nodeC Set.empty (Set.singleton runtimeGroundKey)
      left = graph [a, b, c] [proofGround, runtimeGround] [admissionA]
      right = ProviderQualificationDependencyGraph
        { qualificationDependencyRoots = Set.singleton admissionA
        , qualificationDependencyNodes = Map.fromList
            [ (admissionC, c), (admissionA, a), (admissionB, b) ]
        , qualificationDependencyGroundRegistry = Map.fromList
            [ (runtimeGroundKey, runtimeGround), (proofGroundKey, proofGround) ]
        }
  checkedLeft <- mapLeft show $ checkProviderQualificationDependencyGraph left
  checkedRight <- mapLeft show $ checkProviderQualificationDependencyGraph right
  assert (checkedLeft == checkedRight) "registry insertion order changed closure semantics"

unknownRootRejected :: Either String ()
unknownRootRejected = do
  let missing = QualificationAdmissionRevision "admission:root-missing"
  case checkProviderQualificationDependencyGraph
      (graph [nodeA Set.empty (Set.singleton proofGroundKey)] [proofGround] [missing]) of
    Left (QualificationDependencyUnknownRoot root) ->
      assert (root == missing) "wrong unknown root diagnostic"
    other -> Left ("unknown selected root was accepted: " <> show other)

graph
  :: [ProviderQualificationDependencyNode]
  -> [QualificationGround]
  -> [QualificationAdmissionRevision]
  -> ProviderQualificationDependencyGraph
graph nodes grounds roots = ProviderQualificationDependencyGraph
  { qualificationDependencyRoots = Set.fromList roots
  , qualificationDependencyNodes = Map.fromList
      [ (qualificationDependencyAdmissionRevision node, node) | node <- nodes ]
  , qualificationDependencyGroundRegistry = Map.fromList
      [ (qualificationGroundKey ground, ground) | ground <- grounds ]
  }

nodeA, nodeB, nodeC
  :: Set.Set QualificationAdmissionRevision
  -> Set.Set QualificationGroundKey
  -> ProviderQualificationDependencyNode
nodeA = admittedNode admissionA
nodeB = admittedNode admissionB
nodeC = admittedNode admissionC

admittedNode
  :: QualificationAdmissionRevision
  -> Set.Set QualificationAdmissionRevision
  -> Set.Set QualificationGroundKey
  -> ProviderQualificationDependencyNode
admittedNode revision dependencies grounds = ProviderQualificationDependencyNode
  { qualificationDependencyAdmissionRevision = revision
  , qualificationDependencyAdmissionDecision = QualificationAdmitted
  , qualificationDependencyAdmissions = dependencies
  , qualificationDependencyGrounds = grounds
  }

admissionA, admissionB, admissionC :: QualificationAdmissionRevision
admissionA = QualificationAdmissionRevision "admission:A"
admissionB = QualificationAdmissionRevision "admission:B"
admissionC = QualificationAdmissionRevision "admission:C"

proofGroundKey, runtimeGroundKey, externalGroundKey, assumptionGroundKey
  :: QualificationGroundKey
proofGroundKey = QualificationGroundKey "ground:proof"
runtimeGroundKey = QualificationGroundKey "ground:runtime"
externalGroundKey = QualificationGroundKey "ground:external"
assumptionGroundKey = QualificationGroundKey "ground:assumption"

proofGround, runtimeGround, externalGround, assumptionGround :: QualificationGround
proofGround = acceptedGround proofGroundKey ProofGround "proof:v1"
runtimeGround = acceptedGround runtimeGroundKey RuntimeEnforcementGround "runtime:v1"
externalGround = acceptedGround externalGroundKey ExternalEvidenceGround "external:v1"
assumptionGround = acceptedGround assumptionGroundKey AssumptionGround "assumption:v1"

acceptedGround :: QualificationGroundKey -> QualificationGroundKind -> Text -> QualificationGround
acceptedGround key kind revision = QualificationGround
  { qualificationGroundKey = key
  , qualificationGroundKind = kind
  , qualificationGroundRevision = revision
  , qualificationGroundValidityScope = "phase1-test-scope"
  , qualificationGroundDisposition = QualificationGroundAccepted
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
