{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Static (InstanceRevision (..), RealizationRevision (..))
import Phil.Examples.Phase1.SystemsWitnesses
import Phil.Systems.Phase1Stage
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-001 framed upload passes generic Phase 1 stage verifier" uploadAccepted
    , test "SYS-001 Steve passes the same generic Phase 1 stage verifier" steveAccepted
    , test "SYS-001 both witnesses use the same verifier profile" sameVerifierProfile
    , test "SYS-001 witness systems identities remain distinct" systemsIdentityDistinct
    , test "SYS-001 witness stage identities remain distinct" stageIdentityDistinct
    , test "SYS-001 upload missing source disposition rejects" uploadMissingDispositionRejected
    , test "SYS-001 Steve missing source disposition rejects" steveMissingDispositionRejected
    , test "SYS-001 upload unjustified target mechanism rejects" uploadMissingJustificationRejected
    , test "SYS-001 Steve unjustified target mechanism rejects" steveMissingJustificationRejected
    , test "SYS-001 wrong SystemsArtifactRevision rejects" systemsRevisionMismatchRejected
    , test "SYS-001 wrong StageContractRevision rejects" stageRevisionMismatchRejected
    , test "SYS-001 disposition cannot cite unknown target mechanism" unknownMechanismDispositionRejected
    , test "SYS-001 justification cannot cite unknown source fact" unknownSourceJustificationRejected
    , test "SYS-001 target mechanism requires semantic or realization reason" emptyJustificationRejected
    , test "SYS-001 assumption-dependent disposition requires named assumption" emptyAssumptionDependencyRejected
    , test "SYS-001 canonical revisions are deterministic across reconstruction" deterministicReconstruction
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = mapLeft show $ verifyPhase1StageBundle uploadPhase1StageBundle

steveAccepted :: Either String ()
steveAccepted = do
  steve <- steveBundle
  mapLeft show $ verifyPhase1StageBundle steve

sameVerifierProfile :: Either String ()
sameVerifierProfile = do
  steve <- steveBundle
  assert
    (phase1StageVerifierProfileRevision uploadPhase1StageBundle ==
      phase1StageVerifierProfileRevision steve)
    "the witnesses did not use the same verifier profile"

systemsIdentityDistinct :: Either String ()
systemsIdentityDistinct = do
  steve <- steveBundle
  assert
    (phase1StageSystemsArtifactRevision uploadPhase1StageBundle /=
      phase1StageSystemsArtifactRevision steve)
    "distinct witness Systems graphs collapsed to one identity"

stageIdentityDistinct :: Either String ()
stageIdentityDistinct = do
  steve <- steveBundle
  assert
    (phase1StageContractRevision uploadPhase1StageBundle /=
      phase1StageContractRevision steve)
    "distinct witness stage relations collapsed to one identity"

uploadMissingDispositionRejected :: Either String ()
uploadMissingDispositionRejected =
  missingDispositionRejected uploadPhase1StageBundle

steveMissingDispositionRejected :: Either String ()
steveMissingDispositionRejected = steveBundle >>= missingDispositionRejected

missingDispositionRejected :: Phase1StageBundle -> Either String ()
missingDispositionRejected bundle = do
  key <- firstSet "fixture has no source facts" (phase1StageSourceFacts bundle)
  let reduced = Map.delete key (phase1StageFactDispositions bundle)
      mutated = rebuild bundle reduced (phase1StageSystemsJustifications bundle)
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageDispositionDomainMismatch expected actual) -> do
      assert (expected == phase1StageSourceFacts bundle) "wrong expected source-fact domain"
      assert (actual == Map.keysSet reduced) "wrong reduced disposition domain"
    other -> Left ("missing source disposition was not rejected correctly: " <> show other)

uploadMissingJustificationRejected :: Either String ()
uploadMissingJustificationRejected =
  missingJustificationRejected uploadPhase1StageBundle

steveMissingJustificationRejected :: Either String ()
steveMissingJustificationRejected = steveBundle >>= missingJustificationRejected

missingJustificationRejected :: Phase1StageBundle -> Either String ()
missingJustificationRejected bundle = do
  key <- firstSet "fixture has no Systems mechanisms" (phase1StageSystemsMechanisms bundle)
  let reduced = Map.delete key (phase1StageSystemsJustifications bundle)
      mutated = rebuild bundle (phase1StageFactDispositions bundle) reduced
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageJustificationDomainMismatch expected actual) -> do
      assert (expected == phase1StageSystemsMechanisms bundle) "wrong expected mechanism domain"
      assert (actual == Map.keysSet reduced) "wrong reduced justification domain"
    other -> Left ("missing target justification was not rejected correctly: " <> show other)

systemsRevisionMismatchRejected :: Either String ()
systemsRevisionMismatchRejected = do
  let wrong = SystemsArtifactRevision "systems:wrong"
      mutated = uploadPhase1StageBundle
        { phase1StageSystemsArtifactRevision = wrong }
  case verifyPhase1StageBundle mutated of
    Left (Phase1SystemsArtifactRevisionMismatch expected actual) -> do
      assert (expected == deriveSystemsArtifactRevision
        (phase1StageSystemsArtifact uploadPhase1StageBundle)) "wrong expected Systems revision"
      assert (actual == wrong) "wrong supplied Systems revision"
    other -> Left ("wrong Systems revision was accepted: " <> show other)

stageRevisionMismatchRejected :: Either String ()
stageRevisionMismatchRejected = do
  let wrong = Phase1StageContractRevision "stage:wrong"
      mutated = uploadPhase1StageBundle { phase1StageContractRevision = wrong }
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageContractRevisionMismatch expected actual) -> do
      assert (expected == derivePhase1StageContractRevision uploadPhase1StageBundle)
        "wrong expected StageContract revision"
      assert (actual == wrong) "wrong supplied StageContract revision"
    other -> Left ("wrong StageContract revision was accepted: " <> show other)

unknownMechanismDispositionRejected :: Either String ()
unknownMechanismDispositionRejected = do
  steve <- steveBundle
  fact <- firstSet "Steve fixture has no source facts" (phase1StageSourceFacts steve)
  let unknown = SystemsMechanismKey "unknown:systems:mechanism"
      changed = Map.insert fact (Phase1FactRealized (Set.singleton unknown))
        (phase1StageFactDispositions steve)
      mutated = rebuild steve changed (phase1StageSystemsJustifications steve)
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageDispositionUnknownMechanisms actualFact unknowns) -> do
      assert (actualFact == fact) "wrong fact in unknown-mechanism diagnostic"
      assert (unknowns == Set.singleton unknown) "wrong unknown mechanism set"
    other -> Left ("unknown target mechanism was accepted: " <> show other)

unknownSourceJustificationRejected :: Either String ()
unknownSourceJustificationRejected = do
  steve <- steveBundle
  mechanism <- firstSet "Steve fixture has no Systems mechanisms" (phase1StageSystemsMechanisms steve)
  let unknown = SourceFactKey "unknown.source.fact"
      original = phase1StageSystemsJustifications steve Map.! mechanism
      changedJustification = original
        { systemsJustificationSourceFacts = Set.singleton unknown }
      changed = Map.insert mechanism changedJustification
        (phase1StageSystemsJustifications steve)
      mutated = rebuild steve (phase1StageFactDispositions steve) changed
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageJustificationUnknownSourceFacts actualMechanism unknowns) -> do
      assert (actualMechanism == mechanism) "wrong mechanism in unknown-source diagnostic"
      assert (unknowns == Set.singleton unknown) "wrong unknown source-fact set"
    other -> Left ("unknown source fact was accepted as justification: " <> show other)

emptyJustificationRejected :: Either String ()
emptyJustificationRejected = do
  mechanism <- firstSet "upload fixture has no Systems mechanisms"
    (phase1StageSystemsMechanisms uploadPhase1StageBundle)
  let emptyJustification = SystemsJustification
        { systemsJustificationSourceFacts = Set.empty
        , systemsJustificationRealizationRefs = Set.empty
        , systemsJustificationQualificationRefs = Set.empty
        , systemsJustificationAssumptionRefs = Set.empty
        }
      changed = Map.insert mechanism emptyJustification
        (phase1StageSystemsJustifications uploadPhase1StageBundle)
      mutated = rebuild uploadPhase1StageBundle
        (phase1StageFactDispositions uploadPhase1StageBundle) changed
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageMechanismUnjustified actual) ->
      assert (actual == mechanism) "wrong unjustified target mechanism"
    other -> Left ("empty target justification was accepted: " <> show other)

emptyAssumptionDependencyRejected :: Either String ()
emptyAssumptionDependencyRejected = do
  steve <- steveBundle
  fact <- firstSet "Steve fixture has no source facts" (phase1StageSourceFacts steve)
  let changed = Map.insert fact
        (Phase1FactAssumptionDependent Set.empty
          (Phase1FactRealized (phase1StageSystemsMechanisms steve)))
        (phase1StageFactDispositions steve)
      mutated = rebuild steve changed (phase1StageSystemsJustifications steve)
  case verifyPhase1StageBundle mutated of
    Left (Phase1StageEmptyAssumptionDependency actual) ->
      assert (actual == fact) "wrong fact in empty-assumption diagnostic"
    other -> Left ("empty assumption dependency was accepted: " <> show other)

deterministicReconstruction :: Either String ()
deterministicReconstruction = do
  steve <- steveBundle
  let rebuilt = rebuild steve
        (Map.fromList (reverse (Map.toAscList (phase1StageFactDispositions steve))))
        (Map.fromList (reverse (Map.toAscList (phase1StageSystemsJustifications steve))))
  assert
    (phase1StageSystemsArtifactRevision rebuilt == phase1StageSystemsArtifactRevision steve)
    "Systems revision changed during equivalent reconstruction"
  assert
    (phase1StageContractRevision rebuilt == phase1StageContractRevision steve)
    "StageContract revision changed with map enumeration order"
  mapLeft show $ verifyPhase1StageBundle rebuilt

rebuild
  :: Phase1StageBundle
  -> Map.Map SourceFactKey Phase1FactDisposition
  -> Map.Map SystemsMechanismKey SystemsJustification
  -> Phase1StageBundle
rebuild bundle dispositions justifications = makePhase1StageBundle
  (phase1StageInstanceRevision bundle)
  (phase1StageRealizationRevision bundle)
  (phase1StageVerifierProfileRevision bundle)
  (phase1StageSystemsArtifact bundle)
  dispositions
  justifications

steveBundle :: Either String Phase1StageBundle
steveBundle = stevePhase1StageBundle

firstSet :: String -> Set.Set a -> Either String a
firstSet detail values = case Set.lookupMin values of
  Just value -> Right value
  Nothing -> Left detail

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
