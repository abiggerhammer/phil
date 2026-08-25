{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderQualificationTargetReuse
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-013 semantic claim is reused across distinct legal targets" crossTargetAccepted
    , test "PROV-013 target evidence revision changes across targets" targetEvidenceRevisionChanges
    , test "PROV-013 new target requires fresh translation evidence binding" missingTranslationEvidenceRejected
    , test "PROV-013 wrong semantic claim revision rejects" wrongClaimRevisionRejected
    , test "PROV-013 provider interface drift rejects semantic reuse" interfaceDriftRejected
    , test "PROV-013 implementation revision drift rejects semantic reuse" implementationDriftRejected
    , test "PROV-013 same-target request is not cross-target reuse" sameTargetRejected
    , test "PROV-013 concrete claim cannot masquerade as reusable semantic claim" concreteClaimRejected
    , test "PROV-013 target-specific assumptions revise only target evidence" targetAssumptionChangesEvidenceOnly
    , test "PROV-013 target evidence ordering is nonsemantic" targetEvidenceOrderingCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

crossTargetAccepted :: Either String ()
crossTargetAccepted = do
  checked <- mapLeft show $
    checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wasmEvidence
  assert (checkedCrossTargetClaimRevision checked == semanticClaimRevision)
    "semantic claim revision changed across targets"
  assert (checkedCrossTargetSemanticImplementation checked == providerDefinition)
    "semantic implementation revision changed across targets"

targetEvidenceRevisionChanges :: Either String ()
targetEvidenceRevisionChanges = do
  checked <- mapLeft show $
    checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wasmEvidence
  assert
    (checkedCrossTargetPriorEvidenceRevision checked /=
      checkedCrossTargetNewEvidenceRevision checked)
    "distinct target realization evidence shared one revision"

missingTranslationEvidenceRejected :: Either String ()
missingTranslationEvidenceRejected = do
  let missing = wasmEvidence { targetEvidenceTranslationValidationRefs = Set.empty }
  case checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence missing of
    Left (TargetReuseMissingTranslationEvidence target) ->
      assert (target == "target.wasm32-wasi.v1") "wrong target in missing-evidence error"
    other -> Left ("target without translation evidence was accepted: " <> show other)

wrongClaimRevisionRejected :: Either String ()
wrongClaimRevisionRejected = do
  let wrong = wasmEvidence
        { targetEvidenceClaimRevision = QualificationClaimRevision "claim:other" }
  case checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wrong of
    Left (TargetReuseClaimRevisionMismatch expected actual) -> do
      assert (expected == semanticClaimRevision) "wrong expected claim revision"
      assert (actual == QualificationClaimRevision "claim:other") "wrong actual claim revision"
    other -> Left ("wrong claim revision was accepted: " <> show other)

interfaceDriftRejected :: Either String ()
interfaceDriftRejected = do
  let wrongInterface = InterfaceRevision "provider.blob.v2"
      wrong = wasmEvidence { targetEvidenceRequiredInterface = wrongInterface }
  case checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wrong of
    Left (TargetReuseInterfaceMismatch expected actual) -> do
      assert (expected == providerInterface) "wrong expected interface"
      assert (actual == wrongInterface) "wrong actual interface"
    other -> Left ("interface drift was accepted: " <> show other)

implementationDriftRejected :: Either String ()
implementationDriftRejected = do
  let otherDefinition = DefinitionRevision "provider.blob.impl.v2"
      wrong = wasmEvidence { targetEvidenceSemanticImplementation = otherDefinition }
  case checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wrong of
    Left (TargetReuseImplementationMismatch expected actual) -> do
      assert (expected == providerDefinition) "wrong expected implementation"
      assert (actual == otherDefinition) "wrong actual implementation"
    other -> Left ("implementation drift was accepted: " <> show other)

sameTargetRejected :: Either String ()
sameTargetRejected = do
  let sameTarget = wasmEvidence
        { targetEvidenceTargetProfileRevision = targetEvidenceTargetProfileRevision hostEvidence }
  case checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence sameTarget of
    Left (TargetReuseRequiresDistinctTarget target) ->
      assert (target == "target.host-linux-x86_64.v1") "wrong same-target diagnostic"
    other -> Left ("same target was treated as cross-target reuse: " <> show other)

concreteClaimRejected :: Either String ()
concreteClaimRejected = do
  let concrete = semanticClaim
        { qualificationClaimLayer = ConcreteRealizationQualification
        , qualificationClaimSubject =
            ConcreteProviderRealization providerDefinition "artifact:host-blob"
        }
  case checkProviderCrossTargetSemanticReuse concrete hostEvidence wasmEvidence of
    Left TargetReuseRequiresSemanticImplementationClaim -> Right ()
    other -> Left ("concrete realization claim was reused semantically: " <> show other)

targetAssumptionChangesEvidenceOnly :: Either String ()
targetAssumptionChangesEvidenceOnly = do
  let changed = wasmEvidence
        { targetEvidenceTargetAssumptions = Set.insert "wasi.fs.capability-model.v2"
            (targetEvidenceTargetAssumptions wasmEvidence)
        }
  checkedA <- mapLeft show $
    checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence wasmEvidence
  checkedB <- mapLeft show $
    checkProviderCrossTargetSemanticReuse semanticClaim hostEvidence changed
  assert
    (checkedCrossTargetClaimRevision checkedA == checkedCrossTargetClaimRevision checkedB)
    "target assumption changed semantic claim identity"
  assert
    (checkedCrossTargetNewEvidenceRevision checkedA /= checkedCrossTargetNewEvidenceRevision checkedB)
    "target assumption failed to revise target evidence identity"

targetEvidenceOrderingCanonical :: Either String ()
targetEvidenceOrderingCanonical = do
  let left = wasmEvidence
        { targetEvidenceTranslationValidationRefs = Set.fromList ["tv:b", "tv:a"]
        , targetEvidenceTargetAssumptions = Set.fromList ["assumption:b", "assumption:a"]
        }
      right = wasmEvidence
        { targetEvidenceTranslationValidationRefs = Set.fromList ["tv:a", "tv:b"]
        , targetEvidenceTargetAssumptions = Set.fromList ["assumption:a", "assumption:b"]
        }
  assert
    (deriveTargetRealizationEvidenceRevision left ==
      deriveTargetRealizationEvidenceRevision right)
    "target evidence set ordering changed identity"

semanticClaim :: ProviderQualificationClaimIdentityInput
semanticClaim = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = providerInterface
  , qualificationClaimSubject = SemanticProviderImplementation providerDefinition
  , qualificationClaimLayer = SemanticImplementationQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "qualified:PROV-001-005")
      , ("state", SemanticAtom "qualified:PROV-006")
      , ("laws", SemanticAtom "qualified:PROV-007")
      , ("lifecycle", SemanticAtom "qualified:PROV-008")
      , ("authority", SemanticAtom "qualified:PROV-009")
      ]
  , qualificationClaimConditions = Set.singleton "provider.semantic.conditions.v1"
  , qualificationClaimValidityScope = SemanticAtom "semantic-provider-scope.v1"
  }

semanticClaimRevision :: QualificationClaimRevision
semanticClaimRevision = deriveQualificationClaimRevision semanticClaim

hostEvidence, wasmEvidence :: ProviderTargetRealizationEvidence
hostEvidence = targetEvidence
  "target.host-linux-x86_64.v1"
  "artifact:blob-host-x86_64:v1"
  "abi:host-sysv-x86_64:v1"
  "realization:blob-host:v1"
  (Set.singleton "translation-validation:blob-host:v1")
  (Set.singleton "assumption:linux-filesystem-profile:v1")

wasmEvidence = targetEvidence
  "target.wasm32-wasi.v1"
  "artifact:blob-wasm32-wasi:v1"
  "abi:wasi-preview2:v1"
  "realization:blob-wasi:v1"
  (Set.singleton "translation-validation:blob-wasi:v1")
  (Set.singleton "assumption:wasi-filesystem-profile:v1")

targetEvidence
  :: Text
  -> Text
  -> Text
  -> Text
  -> Set.Set Text
  -> Set.Set Text
  -> ProviderTargetRealizationEvidence
targetEvidence target artifact abi realization translations assumptions =
  ProviderTargetRealizationEvidence
    { targetEvidenceClaimRevision = semanticClaimRevision
    , targetEvidenceRequiredInterface = providerInterface
    , targetEvidenceSemanticImplementation = providerDefinition
    , targetEvidenceTargetProfileRevision = target
    , targetEvidenceArtifactRevision = artifact
    , targetEvidenceRuntimeAbiRevision = abi
    , targetEvidenceRealizationRelationRevision = realization
    , targetEvidenceTranslationValidationRefs = translations
    , targetEvidenceTargetAssumptions = assumptions
    }

providerInterface :: InterfaceRevision
providerInterface = InterfaceRevision "provider.blob.v1"

providerDefinition :: DefinitionRevision
providerDefinition = DefinitionRevision "provider.blob.impl.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
