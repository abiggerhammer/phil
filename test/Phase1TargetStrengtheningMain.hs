{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance.Types (RevisionId (..))
import Phil.Examples.Phase1.AssumptionDependencyWitnesses
  ( steveAssumptionDependencyStage
  , uploadAssumptionDependencyStage
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiObligationRevision
  )
import Phil.Examples.Phase1.TargetStrengtheningWitnesses
import Phil.Systems.AssumptionDependency
  ( verifyAssumptionDependencyStageBundle
  )
import Phil.Systems.TargetStrengthening
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-014 SYS-013 upload predecessor remains valid" uploadAssumptionRegression
    , test "SYS-014 SYS-013 Steve predecessor remains valid" steveAssumptionRegression
    , test "SYS-014 upload with no target strengthening is accepted" uploadNoStrengtheningAccepted
    , test "SYS-014 Steve host ABI strengthening with derived obligation is accepted" steveHostAbiAccepted
    , test "SYS-014 target strengthening cannot disappear from StageContract" strengtheningOmissionRejected
    , test "SYS-014 stronger target fact requires a derived obligation" missingDerivedObligationRejected
    , test "SYS-014 target obligation cannot be relabeled as source assurance" retroactiveSourceAttributionRejected
    , test "SYS-014 derived obligation registry cannot omit a live obligation" derivedRegistryOmissionRejected
    , test "SYS-014 derived obligation retains exact introducer relation" introducedByMismatchRejected
    , test "SYS-014 derived obligation retains exact semantic subjects" subjectMismatchRejected
    , test "SYS-014 derived obligation statement cannot be empty" emptyStatementRejected
    , test "SYS-014 derived obligation acceptance rule cannot be empty" emptyAcceptanceRuleRejected
    , test "SYS-014 lowering-decision derived set must match StageContract relation" decisionDerivedMismatchRejected
    , test "SYS-014 target-strengthening stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAssumptionRegression :: Either String ()
uploadAssumptionRegression = mapLeft show
  (verifyAssumptionDependencyStageBundle uploadAssumptionDependencyStage)

steveAssumptionRegression :: Either String ()
steveAssumptionRegression = do
  bundle <- steveAssumptionDependencyStage
  mapLeft show (verifyAssumptionDependencyStageBundle bundle)

uploadNoStrengtheningAccepted :: Either String ()
uploadNoStrengtheningAccepted = mapLeft show
  (verifyTargetStrengtheningStageBundle uploadTargetStrengtheningStage)

steveHostAbiAccepted :: Either String ()
steveHostAbiAccepted = do
  bundle <- steveTargetStrengtheningStage
  mapLeft show (verifyTargetStrengtheningStageBundle bundle)

strengtheningOmissionRejected :: Either String ()
strengtheningOmissionRejected = do
  original <- steveTargetStrengtheningStage
  let mutated = rebuild original Map.empty Map.empty
  case verifyTargetStrengtheningStageBundle mutated of
    Left (TargetStrengtheningDomainMismatch expected actual)
      | Set.member steveHostAbiStrengtheningRef expected
          && Set.null actual -> Right ()
    other -> Left ("silent target strengthening was accepted: " <> show other)

missingDerivedObligationRejected :: Either String ()
missingDerivedObligationRejected = do
  original <- steveTargetStrengtheningStage
  strengthening <- requireStrengthening original
  let bad = strengthening
        { targetStrengtheningDerivedObligation = Nothing }
      mutated = rebuild original
        (Map.singleton steveHostAbiStrengtheningRef bad)
        Map.empty
  case verifyTargetStrengtheningStageBundle mutated of
    Left (TargetStrengtheningMissingDerivedObligation actual)
      | actual == steveHostAbiStrengtheningRef -> Right ()
    other -> Left ("stronger target fact lacked a derived obligation: " <> show other)

retroactiveSourceAttributionRejected :: Either String ()
retroactiveSourceAttributionRejected = do
  original <- steveTargetStrengtheningStage
  strengthening <- requireStrengthening original
  let bad = strengthening
        { targetStrengtheningSourceAssurance = Set.singleton steveHostAbiObligationRevision
        , targetStrengtheningDerivedObligation = Nothing
        }
      mutated = rebuild original
        (Map.singleton steveHostAbiStrengtheningRef bad)
        Map.empty
  case verifyTargetStrengtheningStageBundle mutated of
    Left (TargetStrengtheningUnknownSourceAssurance actual unknown)
      | actual == steveHostAbiStrengtheningRef
          && unknown == Set.singleton steveHostAbiObligationRevision -> Right ()
    other -> Left ("target obligation was retroactively attributed to source assurance: " <> show other)

derivedRegistryOmissionRejected :: Either String ()
derivedRegistryOmissionRejected = do
  original <- steveTargetStrengtheningStage
  let mutated = rebuild original
        (targetStrengtheningStageFacts original)
        Map.empty
  case verifyTargetStrengtheningStageBundle mutated of
    Left (DerivedObligationRegistryDomainMismatch expected actual)
      | expected == Set.singleton steveHostAbiObligationRevision
          && Set.null actual -> Right ()
    other -> Left ("derived-obligation registry omission was accepted: " <> show other)

introducedByMismatchRejected :: Either String ()
introducedByMismatchRejected = do
  original <- steveTargetStrengtheningStage
  obligation <- requireObligation original
  let bad = obligation { derivedObligationIntroducedBy = Set.empty }
      mutated = rebuild original
        (targetStrengtheningStageFacts original)
        (Map.singleton steveHostAbiObligationRevision bad)
  case verifyTargetStrengtheningStageBundle mutated of
    Left (DerivedObligationIntroducedByMismatch revision expected actual)
      | revision == steveHostAbiObligationRevision
          && expected == Set.singleton steveHostAbiStrengtheningRef
          && Set.null actual -> Right ()
    other -> Left ("derived obligation lost its introducer relation: " <> show other)

subjectMismatchRejected :: Either String ()
subjectMismatchRejected = do
  original <- steveTargetStrengtheningStage
  obligation <- requireObligation original
  let wrong = Set.singleton "steve.blob.wrong-subject"
      bad = obligation { derivedObligationSemanticSubjects = wrong }
      mutated = rebuild original
        (targetStrengtheningStageFacts original)
        (Map.singleton steveHostAbiObligationRevision bad)
  case verifyTargetStrengtheningStageBundle mutated of
    Left (DerivedObligationSubjectMismatch revision expected actual)
      | revision == steveHostAbiObligationRevision
          && expected == Set.singleton "steve.blob.byte-slice"
          && actual == wrong -> Right ()
    other -> Left ("derived obligation accepted wrong semantic subject: " <> show other)

emptyStatementRejected :: Either String ()
emptyStatementRejected = do
  original <- steveTargetStrengtheningStage
  obligation <- requireObligation original
  let bad = obligation { derivedObligationStatement = "" }
      mutated = rebuild original
        (targetStrengtheningStageFacts original)
        (Map.singleton steveHostAbiObligationRevision bad)
  case verifyTargetStrengtheningStageBundle mutated of
    Left (DerivedObligationEmptyStatement revision)
      | revision == steveHostAbiObligationRevision -> Right ()
    other -> Left ("empty derived-obligation statement was accepted: " <> show other)

emptyAcceptanceRuleRejected :: Either String ()
emptyAcceptanceRuleRejected = do
  original <- steveTargetStrengtheningStage
  obligation <- requireObligation original
  let bad = obligation { derivedObligationAcceptanceRule = "" }
      mutated = rebuild original
        (targetStrengtheningStageFacts original)
        (Map.singleton steveHostAbiObligationRevision bad)
  case verifyTargetStrengtheningStageBundle mutated of
    Left (DerivedObligationEmptyAcceptanceRule revision)
      | revision == steveHostAbiObligationRevision -> Right ()
    other -> Left ("empty derived-obligation acceptance rule was accepted: " <> show other)

decisionDerivedMismatchRejected :: Either String ()
decisionDerivedMismatchRejected = do
  original <- steveTargetStrengtheningStage
  strengthening <- requireStrengthening original
  obligation <- requireObligation original
  let wrongRevision = RevisionId "obligation.phase1.steve.host-abi.wrong"
      badStrengthening = strengthening
        { targetStrengtheningDerivedObligation = Just wrongRevision }
      badObligation = obligation
        { derivedObligationRevision = wrongRevision }
      mutated = rebuild original
        (Map.singleton steveHostAbiStrengtheningRef badStrengthening)
        (Map.singleton wrongRevision badObligation)
  case verifyTargetStrengtheningStageBundle mutated of
    Left (TargetStrengtheningDecisionDerivedMismatch _ expected actual)
      | expected == Set.singleton wrongRevision
          && actual == Set.singleton steveHostAbiObligationRevision -> Right ()
    other -> Left ("lowering decision derived-obligation mismatch was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  original <- steveTargetStrengtheningStage
  let rebuilt = rebuild original
        (Map.fromList (reverse (Map.toAscList (targetStrengtheningStageFacts original))))
        (Map.fromList (reverse (Map.toAscList
          (targetStrengtheningStageDerivedObligations original))))
  assert
    (targetStrengtheningStageRevision original
      == targetStrengtheningStageRevision rebuilt)
    "target-strengthening revision changed with map enumeration order"
  mapLeft show (verifyTargetStrengtheningStageBundle rebuilt)

requireStrengthening :: TargetStrengtheningStageBundle -> Either String TargetStrengthening
requireStrengthening bundle = maybe
  (Left "Steve target strengthening missing")
  Right
  (Map.lookup steveHostAbiStrengtheningRef (targetStrengtheningStageFacts bundle))

requireObligation :: TargetStrengtheningStageBundle -> Either String DerivedObligation
requireObligation bundle = maybe
  (Left "Steve host ABI derived obligation missing")
  Right
  (Map.lookup steveHostAbiObligationRevision
    (targetStrengtheningStageDerivedObligations bundle))

rebuild
  :: TargetStrengtheningStageBundle
  -> Map.Map TargetPreconditionRef TargetStrengthening
  -> Map.Map RevisionId DerivedObligation
  -> TargetStrengtheningStageBundle
rebuild original = makeTargetStrengtheningStageBundle
  (targetStrengtheningStageBase original)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
