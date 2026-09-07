{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.ProviderQualificationApplicability
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderQualificationTargetReuse
import Phil.Core.Static
import Phil.Examples.Steve.ProviderQualifications
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R15 genuine Steve admission rechecks identically" genuineAdmissionRechecks
    , test "REVIEW-R15 exact admitted context applies" exactContextAccepted
    , test "REVIEW-R15 stale admission rejects coordinated occurrence relocation" staleOccurrenceRelocationRejected
    , test "REVIEW-R15 stale admission rejects coordinated realization relocation" staleRealizationRelocationRejected
    , test "REVIEW-R15 fresh contextual admission permits genuine relocation" freshContextAdmissionAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

genuineAdmissionRechecks :: Either String ()
genuineAdmissionRechecks = do
  artifact <- blobArtifact
  let claim = steveProviderIdentityClaim artifact
      evidence = steveProviderIdentityEvidence artifact
      admissionInput = steveProviderIdentityAdmission artifact
      checked = steveProviderCheckedAdmission artifact
  rechecked <- mapLeft show $ checkQualificationAdmissionIdentity claim evidence admissionInput
  assert (rechecked == checked) "Steve materializer checked admission differs from direct identity recheck"
  assert
    (checkedQualificationAdmissionProviderOccurrence checked ==
      qualificationAdmissionProviderOccurrence admissionInput)
    "checked admission lost original provider occurrence"
  assert
    (checkedQualificationAdmissionRealizationContextRevision checked ==
      qualificationAdmissionRealizationContextRevision admissionInput)
    "checked admission lost original realization context"

exactContextAccepted :: Either String ()
exactContextAccepted = do
  (checked, targetEvidence, applicability, selected) <- baselineFixture
  result <- mapLeft show $ checkProviderAdmissionApplicability
    checked targetEvidence applicability selected
  assert
    (checkedProviderApplicabilityRequirementOccurrence result ==
      providerApplicabilityRequirementOccurrence applicability)
    "checked applicability lost exact requirement occurrence"

staleOccurrenceRelocationRejected :: Either String ()
staleOccurrenceRelocationRejected = do
  (checked, targetEvidence, applicability, selected) <- baselineFixture
  let relocated = ProviderRequirementOccurrenceKey "steve.relocated-provider"
      badApplicability = applicability
        { providerApplicabilityRequirementOccurrence = relocated }
      badSelected = selected
        { selectedProviderRequirementOccurrence = relocated }
  case checkProviderAdmissionApplicability
      checked targetEvidence badApplicability badSelected of
    Left (ProviderApplicabilityAdmissionOccurrenceMismatch expected actual) -> do
      assert
        (expected == checkedQualificationAdmissionProviderOccurrence checked)
        "wrong original provider occurrence in R15 rejection"
      assert
        (actual == unProviderRequirementOccurrenceKey relocated)
        "wrong relocated provider occurrence in R15 rejection"
    other -> Left ("coordinated occurrence relocation under stale admission was accepted: " <> show other)

staleRealizationRelocationRejected :: Either String ()
staleRealizationRelocationRejected = do
  (checked, targetEvidence, applicability, selected) <- baselineFixture
  let relocated = RealizationRevision "steve.relocated-realization-context"
      badApplicability = applicability
        { providerApplicabilityRealizationRevision = relocated }
      badSelected = selected
        { selectedProviderRealizationRevision = relocated }
  case checkProviderAdmissionApplicability
      checked targetEvidence badApplicability badSelected of
    Left (ProviderApplicabilityAdmissionRealizationContextMismatch expected actual) -> do
      assert
        (expected == checkedQualificationAdmissionRealizationContextRevision checked)
        "wrong original realization context in R15 rejection"
      assert
        (actual == realizationText relocated)
        "wrong relocated realization context in R15 rejection"
    other -> Left ("coordinated realization relocation under stale admission was accepted: " <> show other)

freshContextAdmissionAccepted :: Either String ()
freshContextAdmissionAccepted = do
  artifact <- blobArtifact
  let claim = steveProviderIdentityClaim artifact
      evidence = steveProviderIdentityEvidence artifact
      priorInput = steveProviderIdentityAdmission artifact
      freshOccurrence = "steve.relocated-provider"
      freshContext = "steve.relocated-realization-context"
      freshInput = priorInput
        { qualificationAdmissionProviderOccurrence = freshOccurrence
        , qualificationAdmissionRealizationContextRevision = freshContext
        }
  freshChecked <- mapLeft show $ checkQualificationAdmissionIdentity claim evidence freshInput
  priorChecked <- mapLeft show $ checkQualificationAdmissionIdentity claim evidence priorInput
  assert
    (checkedQualificationAdmissionRevision freshChecked /=
      checkedQualificationAdmissionRevision priorChecked)
    "genuine context change did not produce a fresh admission revision"
  targetEvidence <- targetEvidenceFor artifact freshChecked
  let applicability = applicabilityFor freshChecked targetEvidence
      selected = selectedFor applicability
  _ <- mapLeft show $ checkProviderAdmissionApplicability
    freshChecked targetEvidence applicability selected
  Right ()

baselineFixture
  :: Either String
       ( CheckedProviderQualificationAdmissionIdentity
       , ProviderTargetRealizationEvidence
       , ProviderConcreteAdmissionApplicability
       , SelectedProviderRealization
       )
baselineFixture = do
  artifact <- blobArtifact
  let claim = steveProviderIdentityClaim artifact
      evidence = steveProviderIdentityEvidence artifact
      admissionInput = steveProviderIdentityAdmission artifact
  checked <- mapLeft show $ checkQualificationAdmissionIdentity claim evidence admissionInput
  assert (checked == steveProviderCheckedAdmission artifact)
    "baseline did not use genuine Steve checked admission"
  targetEvidence <- targetEvidenceFor artifact checked
  let applicability = applicabilityFor checked targetEvidence
      selected = selectedFor applicability
  Right (checked, targetEvidence, applicability, selected)

blobArtifact :: Either String SteveProviderQualificationArtifact
blobArtifact = do
  qualifications <- mapLeft (Text.unpack . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  Right (steveBlobProviderQualification qualifications)

targetEvidenceFor
  :: SteveProviderQualificationArtifact
  -> CheckedProviderQualificationAdmissionIdentity
  -> Either String ProviderTargetRealizationEvidence
targetEvidenceFor artifact checked = do
  definition <- semanticDefinition (qualificationClaimSubject (steveProviderIdentityClaim artifact))
  Right ProviderTargetRealizationEvidence
    { targetEvidenceClaimRevision = checkedQualificationAdmissionClaimRevision checked
    , targetEvidenceRequiredInterface =
        qualificationClaimRequiredInterface (steveProviderIdentityClaim artifact)
    , targetEvidenceSemanticImplementation = definition
    , targetEvidenceTargetProfileRevision = "review-r15.target.host.v1"
    , targetEvidenceArtifactRevision = "review-r15.artifact.v1"
    , targetEvidenceRuntimeAbiRevision = "review-r15.abi.v1"
    , targetEvidenceRealizationRelationRevision = "review-r15.realization-relation.v1"
    , targetEvidenceTranslationValidationRefs = Set.singleton "review-r15.translation.v1"
    , targetEvidenceTargetAssumptions = Set.singleton "review-r15.target-assumption.v1"
    }

applicabilityFor
  :: CheckedProviderQualificationAdmissionIdentity
  -> ProviderTargetRealizationEvidence
  -> ProviderConcreteAdmissionApplicability
applicabilityFor checked targetEvidence = ProviderConcreteAdmissionApplicability
  { providerApplicabilityAdmissionRevision = checkedQualificationAdmissionRevision checked
  , providerApplicabilityClaimRevision = checkedQualificationAdmissionClaimRevision checked
  , providerApplicabilityTargetEvidenceRevision = deriveTargetRealizationEvidenceRevision targetEvidence
  , providerApplicabilityRequirementOccurrence = ProviderRequirementOccurrenceKey
      (checkedQualificationAdmissionProviderOccurrence checked)
  , providerApplicabilityInstanceRevision = InstanceRevision "review-r15.instance.v1"
  , providerApplicabilityRealizationRevision = RealizationRevision
      (checkedQualificationAdmissionRealizationContextRevision checked)
  , providerApplicabilityRequiredInterface = targetEvidenceRequiredInterface targetEvidence
  , providerApplicabilityImplementationDefinition = targetEvidenceSemanticImplementation targetEvidence
  , providerApplicabilityTargetProfileRevision = targetEvidenceTargetProfileRevision targetEvidence
  , providerApplicabilityArtifactRevision = targetEvidenceArtifactRevision targetEvidence
  , providerApplicabilityRuntimeAbiRevision = targetEvidenceRuntimeAbiRevision targetEvidence
  , providerApplicabilityExportedSymbols = Set.singleton "review_r15_provider_entry"
  }

selectedFor :: ProviderConcreteAdmissionApplicability -> SelectedProviderRealization
selectedFor applicability = SelectedProviderRealization
  { selectedProviderAdmissionRevision = providerApplicabilityAdmissionRevision applicability
  , selectedProviderTargetEvidenceRevision = providerApplicabilityTargetEvidenceRevision applicability
  , selectedProviderRequirementOccurrence = providerApplicabilityRequirementOccurrence applicability
  , selectedProviderInstanceRevision = providerApplicabilityInstanceRevision applicability
  , selectedProviderRealizationRevision = providerApplicabilityRealizationRevision applicability
  , selectedProviderRequiredInterface = providerApplicabilityRequiredInterface applicability
  , selectedProviderImplementationDefinition = providerApplicabilityImplementationDefinition applicability
  , selectedProviderTargetProfileRevision = providerApplicabilityTargetProfileRevision applicability
  , selectedProviderArtifactRevision = providerApplicabilityArtifactRevision applicability
  , selectedProviderRuntimeAbiRevision = providerApplicabilityRuntimeAbiRevision applicability
  , selectedProviderExportedSymbols = Set.singleton "review_r15_backend_symbol"
  }

semanticDefinition :: ProviderQualificationSubject -> Either String DefinitionRevision
semanticDefinition subject = case subject of
  SemanticProviderImplementation definition -> Right definition
  ConcreteProviderRealization definition _ -> Right definition
  OpaqueProviderBoundary name -> Left
    ("R15 genuine Steve fixture unexpectedly used opaque provider boundary: " <> Text.unpack name)

realizationText :: RealizationRevision -> Text.Text
realizationText (RealizationRevision value) = value

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
