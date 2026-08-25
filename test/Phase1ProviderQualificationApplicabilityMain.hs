{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.ProviderQualificationApplicability
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderQualificationTargetReuse
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-014 exact admission applies to exact selected realization" exactSelectionAccepted
    , test "PROV-014 matching symbols cannot rescue wrong artifact" artifactMismatchRejected
    , test "PROV-014 matching symbols cannot rescue wrong target profile" targetProfileMismatchRejected
    , test "PROV-014 matching symbols cannot rescue wrong runtime ABI" runtimeAbiMismatchRejected
    , test "PROV-014 selected realization revision is exact" realizationRevisionMismatchRejected
    , test "PROV-014 selected instance revision is exact" instanceRevisionMismatchRejected
    , test "PROV-014 provider requirement occurrence is exact" occurrenceMismatchRejected
    , test "PROV-014 implementation definition is exact" implementationMismatchRejected
    , test "PROV-014 provider interface is exact" interfaceMismatchRejected
    , test "PROV-014 admission revision is exact" admissionMismatchRejected
    , test "PROV-014 target evidence revision is exact" targetEvidenceMismatchRejected
    , test "PROV-014 rejected admission cannot justify realization" rejectedAdmissionRejected
    , test "PROV-014 symbol rename alone is nonsemantic" symbolRenameAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactSelectionAccepted :: Either String ()
exactSelectionAccepted = do
  checked <- mapLeft show $ checkProviderAdmissionApplicability
    admitted targetEvidence applicability selected
  assert (checkedProviderApplicabilityAdmissionRevision checked == admissionRevision)
    "checked applicability lost admission revision"
  assert (checkedProviderApplicabilityRealizationRevision checked == realizationRevision)
    "checked applicability lost realization revision"

artifactMismatchRejected :: Either String ()
artifactMismatchRejected = case checkProviderAdmissionApplicability
    admitted targetEvidence applicability
    (selected { selectedProviderArtifactRevision = "artifact:other" }) of
  Left (ProviderApplicabilityArtifactMismatch expected actual) -> do
    assert (expected == artifactRevision) "wrong expected artifact"
    assert (actual == "artifact:other") "wrong selected artifact"
  other -> Left ("wrong artifact with matching symbols was accepted: " <> show other)

targetProfileMismatchRejected :: Either String ()
targetProfileMismatchRejected = case checkProviderAdmissionApplicability
    admitted targetEvidence applicability
    (selected { selectedProviderTargetProfileRevision = "target:other" }) of
  Left (ProviderApplicabilityTargetProfileMismatch expected actual) -> do
    assert (expected == targetProfile) "wrong expected target profile"
    assert (actual == "target:other") "wrong selected target profile"
  other -> Left ("wrong target with matching symbols was accepted: " <> show other)

runtimeAbiMismatchRejected :: Either String ()
runtimeAbiMismatchRejected = case checkProviderAdmissionApplicability
    admitted targetEvidence applicability
    (selected { selectedProviderRuntimeAbiRevision = "abi:other" }) of
  Left (ProviderApplicabilityRuntimeAbiMismatch expected actual) -> do
    assert (expected == runtimeAbi) "wrong expected runtime ABI"
    assert (actual == "abi:other") "wrong selected runtime ABI"
  other -> Left ("wrong ABI with matching symbols was accepted: " <> show other)

realizationRevisionMismatchRejected :: Either String ()
realizationRevisionMismatchRejected = do
  let other = RealizationRevision "realization:other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderRealizationRevision = other }) of
    Left (ProviderApplicabilityRealizationRevisionMismatch expected actual) -> do
      assert (expected == realizationRevision) "wrong expected realization revision"
      assert (actual == other) "wrong selected realization revision"
    otherResult -> Left ("wrong realization revision was accepted: " <> show otherResult)

instanceRevisionMismatchRejected :: Either String ()
instanceRevisionMismatchRejected = do
  let other = InstanceRevision "instance:other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderInstanceRevision = other }) of
    Left (ProviderApplicabilityInstanceRevisionMismatch expected actual) -> do
      assert (expected == instanceRevision) "wrong expected instance revision"
      assert (actual == other) "wrong selected instance revision"
    otherResult -> Left ("wrong instance revision was accepted: " <> show otherResult)

occurrenceMismatchRejected :: Either String ()
occurrenceMismatchRejected = do
  let other = ProviderRequirementOccurrenceKey "provider.requirement.other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderRequirementOccurrence = other }) of
    Left (ProviderApplicabilityRequirementOccurrenceMismatch expected actual) -> do
      assert (expected == requirementOccurrence) "wrong expected provider occurrence"
      assert (actual == other) "wrong selected provider occurrence"
    otherResult -> Left ("wrong provider occurrence was accepted: " <> show otherResult)

implementationMismatchRejected :: Either String ()
implementationMismatchRejected = do
  let other = DefinitionRevision "provider.impl.other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderImplementationDefinition = other }) of
    Left (ProviderApplicabilityImplementationMismatch expected actual) -> do
      assert (expected == implementationRevision) "wrong expected implementation"
      assert (actual == other) "wrong selected implementation"
    otherResult -> Left ("wrong implementation was accepted: " <> show otherResult)

interfaceMismatchRejected :: Either String ()
interfaceMismatchRejected = do
  let other = InterfaceRevision "provider.interface.other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderRequiredInterface = other }) of
    Left (ProviderApplicabilityInterfaceMismatch expected actual) -> do
      assert (expected == interfaceRevision) "wrong expected interface"
      assert (actual == other) "wrong selected interface"
    otherResult -> Left ("wrong interface was accepted: " <> show otherResult)

admissionMismatchRejected :: Either String ()
admissionMismatchRejected = do
  let other = QualificationAdmissionRevision "admission:other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderAdmissionRevision = other }) of
    Left (ProviderApplicabilitySelectionAdmissionMismatch expected actual) -> do
      assert (expected == admissionRevision) "wrong expected admission revision"
      assert (actual == other) "wrong selected admission revision"
    otherResult -> Left ("wrong admission was accepted: " <> show otherResult)

targetEvidenceMismatchRejected :: Either String ()
targetEvidenceMismatchRejected = do
  let other = TargetRealizationEvidenceRevision "target-evidence:other"
  case checkProviderAdmissionApplicability admitted targetEvidence applicability
      (selected { selectedProviderTargetEvidenceRevision = other }) of
    Left (ProviderApplicabilitySelectionTargetEvidenceMismatch expected actual) -> do
      assert (expected == targetEvidenceRevision) "wrong expected target evidence revision"
      assert (actual == other) "wrong selected target evidence revision"
    otherResult -> Left ("wrong target evidence was accepted: " <> show otherResult)

rejectedAdmissionRejected :: Either String ()
rejectedAdmissionRejected = case checkProviderAdmissionApplicability
    rejected targetEvidence applicability selected of
  Left ProviderApplicabilityAdmissionRejected -> Right ()
  other -> Left ("rejected admission justified realization: " <> show other)

symbolRenameAccepted :: Either String ()
symbolRenameAccepted = do
  let renamedApplicability = applicability
        { providerApplicabilityExportedSymbols = Set.singleton "renamed_provider_entry" }
      renamedSelection = selected
        { selectedProviderExportedSymbols = Set.singleton "another_backend_symbol" }
  _ <- mapLeft show $ checkProviderAdmissionApplicability
    admitted targetEvidence renamedApplicability renamedSelection
  Right ()

admitted, rejected :: CheckedProviderQualificationAdmissionIdentity
admitted = CheckedProviderQualificationAdmissionIdentity
  { checkedQualificationAdmissionClaimRevision = claimRevision
  , checkedQualificationAdmissionEvidenceRevision = QualificationEvidenceRevision "evidence:v1"
  , checkedQualificationAdmissionRevision = admissionRevision
  , checkedQualificationAdmissionDecision = QualificationAdmitted
  }
rejected = admitted
  { checkedQualificationAdmissionDecision = QualificationRejected (Set.singleton "policy-rejected") }

targetEvidence :: ProviderTargetRealizationEvidence
targetEvidence = ProviderTargetRealizationEvidence
  { targetEvidenceClaimRevision = claimRevision
  , targetEvidenceRequiredInterface = interfaceRevision
  , targetEvidenceSemanticImplementation = implementationRevision
  , targetEvidenceTargetProfileRevision = targetProfile
  , targetEvidenceArtifactRevision = artifactRevision
  , targetEvidenceRuntimeAbiRevision = runtimeAbi
  , targetEvidenceRealizationRelationRevision = "realization-relation:v1"
  , targetEvidenceTranslationValidationRefs = Set.singleton "translation-validation:v1"
  , targetEvidenceTargetAssumptions = Set.singleton "assumption:target:v1"
  }

targetEvidenceRevision :: TargetRealizationEvidenceRevision
targetEvidenceRevision = deriveTargetRealizationEvidenceRevision targetEvidence

applicability :: ProviderConcreteAdmissionApplicability
applicability = ProviderConcreteAdmissionApplicability
  { providerApplicabilityAdmissionRevision = admissionRevision
  , providerApplicabilityClaimRevision = claimRevision
  , providerApplicabilityTargetEvidenceRevision = targetEvidenceRevision
  , providerApplicabilityRequirementOccurrence = requirementOccurrence
  , providerApplicabilityInstanceRevision = instanceRevision
  , providerApplicabilityRealizationRevision = realizationRevision
  , providerApplicabilityRequiredInterface = interfaceRevision
  , providerApplicabilityImplementationDefinition = implementationRevision
  , providerApplicabilityTargetProfileRevision = targetProfile
  , providerApplicabilityArtifactRevision = artifactRevision
  , providerApplicabilityRuntimeAbiRevision = runtimeAbi
  , providerApplicabilityExportedSymbols = Set.singleton "blob_provider_entry"
  }

selected :: SelectedProviderRealization
selected = SelectedProviderRealization
  { selectedProviderAdmissionRevision = admissionRevision
  , selectedProviderTargetEvidenceRevision = targetEvidenceRevision
  , selectedProviderRequirementOccurrence = requirementOccurrence
  , selectedProviderInstanceRevision = instanceRevision
  , selectedProviderRealizationRevision = realizationRevision
  , selectedProviderRequiredInterface = interfaceRevision
  , selectedProviderImplementationDefinition = implementationRevision
  , selectedProviderTargetProfileRevision = targetProfile
  , selectedProviderArtifactRevision = artifactRevision
  , selectedProviderRuntimeAbiRevision = runtimeAbi
  , selectedProviderExportedSymbols = Set.singleton "blob_provider_entry"
  }

claimRevision :: QualificationClaimRevision
claimRevision = QualificationClaimRevision "provider-claim:v1"

admissionRevision :: QualificationAdmissionRevision
admissionRevision = QualificationAdmissionRevision "provider-admission:v1"

requirementOccurrence :: ProviderRequirementOccurrenceKey
requirementOccurrence = ProviderRequirementOccurrenceKey "provider.requirement.blob"

instanceRevision :: InstanceRevision
instanceRevision = InstanceRevision "architecture.instance:v1"

realizationRevision :: RealizationRevision
realizationRevision = RealizationRevision "architecture.realization:v1"

interfaceRevision :: InterfaceRevision
interfaceRevision = InterfaceRevision "provider.blob:v1"

implementationRevision :: DefinitionRevision
implementationRevision = DefinitionRevision "provider.blob.impl:v1"

targetProfile, artifactRevision, runtimeAbi :: String
targetProfile = "target.host-linux-x86_64:v1"
artifactRevision = "artifact:blob-host:v1"
runtimeAbi = "abi:host-sysv-x86_64:v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
