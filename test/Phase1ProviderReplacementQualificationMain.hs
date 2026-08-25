{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderReplacementQualification
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-015 independently qualified replacement accepts" independentAccepts
    , test "PROV-015 preserves provider occurrence and ArchitectureInstance" abstractBindingPreserved
    , test "PROV-015 changes claim/evidence/admission/realization lineage" lineageChanges
    , test "PROV-015 inherited evidence without cross-claim scope rejects" inheritedEvidenceRejects
    , test "PROV-015 explicitly reusable evidence may apply to both claims" explicitReuseAccepts
    , test "PROV-015 evidence reuse requires nonempty validity scope" emptyReuseScopeRejects
    , test "PROV-015 same implementation subject is not replacement" sameSubjectRejects
    , test "PROV-015 public provider interface must remain fixed" interfaceChangeRejects
    , test "PROV-015 provider occurrence must remain fixed" occurrenceChangeRejects
    , test "PROV-015 ArchitectureInstance must remain fixed" instanceChangeRejects
    , test "PROV-015 RealizationRevision must change" unchangedRealizationRejects
    , test "PROV-015 predecessor evidence bundle cannot qualify replacement" predecessorEvidenceRejects
    , test "PROV-015 predecessor admission cannot be inherited" predecessorAdmissionRejects
    , test "PROV-015 rejected replacement admission cannot be selected" rejectedReplacementRejects
    , test "PROV-015 replacement may cross semantic/opaque qualification layers" crossLayerAccepts
    , test "PROV-015 reuse justification must name actually shared evidence" unexpectedReuseRejects
    , test "PROV-015 reuse justification binds exact replacement claim" wrongReuseClaimRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

independentAccepts :: Either String ()
independentAccepts = do
  _ <- checked priorSide replacementSide Map.empty
  Right ()

abstractBindingPreserved :: Either String ()
abstractBindingPreserved = do
  result <- checked priorSide replacementSide Map.empty
  assert (checkedProviderReplacementRequiredInterface result == providerInterface)
    "provider interface changed"
  assert (checkedProviderReplacementOccurrence result == providerOccurrence)
    "provider occurrence changed"
  assert (checkedProviderReplacementInstanceRevision result == instanceRevision)
    "ArchitectureInstance changed"

lineageChanges :: Either String ()
lineageChanges = do
  result <- checked priorSide replacementSide Map.empty
  assert (checkedProviderReplacementPriorClaimRevision result /= checkedProviderReplacementNewClaimRevision result)
    "claim revision was inherited"
  assert (checkedProviderReplacementPriorEvidenceRevision result /= checkedProviderReplacementNewEvidenceRevision result)
    "evidence revision was inherited"
  assert (checkedProviderReplacementPriorAdmissionRevision result /= checkedProviderReplacementNewAdmissionRevision result)
    "admission revision was inherited"
  assert (checkedProviderReplacementPriorRealizationRevision result /= checkedProviderReplacementNewRealizationRevision result)
    "realization revision was inherited"

inheritedEvidenceRejects :: Either String ()
inheritedEvidenceRejects = do
  let p = withProof priorSide sharedProof
      n = withProof replacementSide sharedProof
      ref = proofRef sharedProof
  case checkProviderReplacementQualification p n Map.empty of
    Left (ProviderReplacementSharedEvidenceWithoutScope refs) ->
      assert (refs == Set.singleton ref) "wrong shared-evidence diagnostic"
    other -> Left ("inherited evidence accepted: " <> show other)

explicitReuseAccepts :: Either String ()
explicitReuseAccepts = do
  let p = withProof priorSide sharedProof
      n = withProof replacementSide sharedProof
      ref = proofRef sharedProof
      reuse = ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = claimRevisionOf p
        , providerReplacementReuseNewClaimRevision = claimRevisionOf n
        , providerReplacementReuseValidityScopeRevision = "validity:shared-proof-covers-both:v1"
        }
  result <- checked p n (Map.singleton ref reuse)
  assert (checkedProviderReplacementReusedEvidence result == Set.singleton ref)
    "shared evidence was not retained"

emptyReuseScopeRejects :: Either String ()
emptyReuseScopeRejects = do
  let p = withProof priorSide sharedProof
      n = withProof replacementSide sharedProof
      ref = proofRef sharedProof
      reuse = ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = claimRevisionOf p
        , providerReplacementReuseNewClaimRevision = claimRevisionOf n
        , providerReplacementReuseValidityScopeRevision = ""
        }
  case checkProviderReplacementQualification p n (Map.singleton ref reuse) of
    Left (ProviderReplacementReuseScopeMissing actual) ->
      assert (actual == ref) "wrong missing-scope diagnostic"
    other -> Left ("empty reuse scope accepted: " <> show other)

sameSubjectRejects :: Either String ()
sameSubjectRejects = do
  let claim = priorClaim
      evidence = evidenceFor claim "proof:i1-second"
      side = replacementSide
        { providerReplacementClaim = claim
        , providerReplacementEvidence = evidence
        , providerReplacementAdmission = admissionFor claim evidence "artifact:i1-second"
        }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementSameImplementationSubject subject) ->
      assert (subject == qualificationClaimSubject priorClaim) "wrong subject"
    other -> Left ("same subject treated as replacement: " <> show other)

interfaceChangeRejects :: Either String ()
interfaceChangeRejects = do
  let claim = replacementClaim { qualificationClaimRequiredInterface = InterfaceRevision "provider.blob:v2" }
      evidence = evidenceFor claim "proof:i2-v2"
      side = replacementSide
        { providerReplacementClaim = claim
        , providerReplacementEvidence = evidence
        , providerReplacementAdmission = admissionFor claim evidence "artifact:i2-v2"
        }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementInterfaceMismatch expected actual) -> do
      assert (expected == providerInterface) "wrong expected interface"
      assert (actual == InterfaceRevision "provider.blob:v2") "wrong actual interface"
    other -> Left ("interface-changing replacement accepted: " <> show other)

occurrenceChangeRejects :: Either String ()
occurrenceChangeRejects = do
  let admission = (providerReplacementAdmission replacementSide)
        { qualificationAdmissionProviderOccurrence = "provider.requirement.other" }
      side = replacementSide { providerReplacementAdmission = admission }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementOccurrenceMismatch expected actual) -> do
      assert (expected == providerOccurrence) "wrong expected occurrence"
      assert (actual == "provider.requirement.other") "wrong actual occurrence"
    other -> Left ("occurrence-changing replacement accepted: " <> show other)

instanceChangeRejects :: Either String ()
instanceChangeRejects = do
  let otherInstance = InstanceRevision "architecture.instance:other"
      side = replacementSide { providerReplacementInstanceRevision = otherInstance }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementInstanceMismatch expected actual) -> do
      assert (expected == instanceRevision) "wrong expected instance"
      assert (actual == otherInstance) "wrong actual instance"
    other -> Left ("instance-changing replacement accepted: " <> show other)

unchangedRealizationRejects :: Either String ()
unchangedRealizationRejects = do
  let side = replacementSide { providerReplacementRealizationRevision = priorRealizationRevision }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementRealizationUnchanged revision) ->
      assert (revision == priorRealizationRevision) "wrong realization diagnostic"
    other -> Left ("unchanged realization accepted: " <> show other)

predecessorEvidenceRejects :: Either String ()
predecessorEvidenceRejects = do
  let side = replacementSide { providerReplacementEvidence = providerReplacementEvidence priorSide }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementNewIdentityError (QualificationEvidenceClaimRevisionMismatch _ actual)) ->
      assert (actual == claimRevisionOf priorSide) "wrong inherited claim revision"
    other -> Left ("predecessor evidence bundle accepted: " <> show other)

predecessorAdmissionRejects :: Either String ()
predecessorAdmissionRejects = do
  let side = replacementSide { providerReplacementAdmission = providerReplacementAdmission priorSide }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementNewIdentityError _) -> Right ()
    other -> Left ("predecessor admission accepted: " <> show other)

rejectedReplacementRejects :: Either String ()
rejectedReplacementRejects = do
  let admission = (providerReplacementAdmission replacementSide)
        { qualificationAdmissionDecision = QualificationRejected (Set.singleton "policy-rejected") }
      side = replacementSide { providerReplacementAdmission = admission }
  case checkProviderReplacementQualification priorSide side Map.empty of
    Left (ProviderReplacementNewAdmissionRejected reasons) ->
      assert (reasons == Set.singleton "policy-rejected") "wrong rejection reasons"
    other -> Left ("rejected replacement accepted: " <> show other)

crossLayerAccepts :: Either String ()
crossLayerAccepts = do
  let claim = claimFor (OpaqueProviderBoundary "opaque-service:blob:v1") CollapsedOpaqueQualification
      evidence = evidenceFor claim "evidence:opaque-blob:v1"
      side = replacementSide
        { providerReplacementClaim = claim
        , providerReplacementEvidence = evidence
        , providerReplacementAdmission = admissionFor claim evidence "opaque-service:blob:v1"
        }
  _ <- checked priorSide side Map.empty
  Right ()

unexpectedReuseRejects :: Either String ()
unexpectedReuseRejects = do
  let ref = proofRef "proof:not-shared"
      reuse = ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = claimRevisionOf priorSide
        , providerReplacementReuseNewClaimRevision = claimRevisionOf replacementSide
        , providerReplacementReuseValidityScopeRevision = "validity:v1"
        }
  case checkProviderReplacementQualification priorSide replacementSide (Map.singleton ref reuse) of
    Left (ProviderReplacementUnexpectedReuseJustification refs) ->
      assert (refs == Set.singleton ref) "wrong unexpected-reuse diagnostic"
    other -> Left ("unshared reuse justification accepted: " <> show other)

wrongReuseClaimRejects :: Either String ()
wrongReuseClaimRejects = do
  let p = withProof priorSide sharedProof
      n = withProof replacementSide sharedProof
      ref = proofRef sharedProof
      wrongClaim = QualificationClaimRevision "claim:wrong"
      reuse = ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = claimRevisionOf p
        , providerReplacementReuseNewClaimRevision = wrongClaim
        , providerReplacementReuseValidityScopeRevision = "validity:v1"
        }
  case checkProviderReplacementQualification p n (Map.singleton ref reuse) of
    Left (ProviderReplacementReuseNewClaimMismatch expected actual) -> do
      assert (expected == claimRevisionOf n) "wrong expected replacement claim"
      assert (actual == wrongClaim) "wrong actual replacement claim"
    other -> Left ("reuse with wrong claim accepted: " <> show other)

checked
  :: ProviderReplacementSide
  -> ProviderReplacementSide
  -> Map.Map ProviderReplacementEvidenceReference ProviderReplacementEvidenceReuse
  -> Either String CheckedProviderReplacementQualification
checked p n reuse = mapLeft show (checkProviderReplacementQualification p n reuse)

priorSide, replacementSide :: ProviderReplacementSide
priorSide = sideFor priorClaim "proof:i1-provider-law" "artifact:blob:i1" priorRealizationRevision
replacementSide = sideFor replacementClaim "proof:i2-provider-law" "artifact:blob:i2" replacementRealizationRevision

sideFor :: ProviderQualificationClaimIdentityInput -> Text -> Text -> RealizationRevision -> ProviderReplacementSide
sideFor claim proof artifact realization =
  let evidence = evidenceFor claim proof
  in ProviderReplacementSide
      { providerReplacementClaim = claim
      , providerReplacementEvidence = evidence
      , providerReplacementAdmission = admissionFor claim evidence artifact
      , providerReplacementInstanceRevision = instanceRevision
      , providerReplacementRealizationRevision = realization
      }

withProof :: ProviderReplacementSide -> Text -> ProviderReplacementSide
withProof side proof =
  let claim = providerReplacementClaim side
      evidence = evidenceFor claim proof
      artifact = maybe "artifact:missing" id
        (qualificationAdmissionSelectedArtifactRuntimeAbi (providerReplacementAdmission side))
  in side
      { providerReplacementEvidence = evidence
      , providerReplacementAdmission = admissionFor claim evidence artifact
      }

priorClaim, replacementClaim :: ProviderQualificationClaimIdentityInput
priorClaim = claimFor (SemanticProviderImplementation (DefinitionRevision "provider.blob.impl:i1")) SemanticImplementationQualification
replacementClaim = claimFor (SemanticProviderImplementation (DefinitionRevision "provider.blob.impl:i2")) SemanticImplementationQualification

claimFor :: ProviderQualificationSubject -> ProviderQualificationLayer -> ProviderQualificationClaimIdentityInput
claimFor subject layer = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = providerInterface
  , qualificationClaimSubject = subject
  , qualificationClaimLayer = layer
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "blob.read+install-if-absent")
      , ("provider-law", SemanticAtom "no-replace:v1")
      ]
  , qualificationClaimConditions = Set.singleton "condition:phase1-provider:v1"
  , qualificationClaimValidityScope = SemanticAtom "provider-validity:v1"
  }

evidenceFor :: ProviderQualificationClaimIdentityInput -> Text -> ProviderQualificationEvidenceIdentityInput
evidenceFor claim proof = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision claim
  , qualificationEvidenceObligationDispositions = Map.singleton
      "provider-law.no-replace" (SemanticAtom "discharged-by-evidence")
  , qualificationEvidenceRefs = Set.empty
  , qualificationEvidenceProofRefs = Set.singleton proof
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs = Set.empty
  , qualificationEvidenceAssumptionRefs = Set.empty
  , qualificationEvidenceValidityDependencies = Set.empty
  }

admissionFor
  :: ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> Text
  -> ProviderQualificationAdmissionIdentityInput
admissionFor claim evidence artifact = ProviderQualificationAdmissionIdentityInput
  { qualificationAdmissionClaimRevision = deriveQualificationClaimRevision claim
  , qualificationAdmissionEvidenceRevision = deriveQualificationEvidenceRevision evidence
  , qualificationAdmissionProviderOccurrence = providerOccurrence
  , qualificationAdmissionRequiredInterface = qualificationClaimRequiredInterface claim
  , qualificationAdmissionRealizationContextRevision = "realization-context:v1"
  , qualificationAdmissionAssurancePolicyRevision = "assurance-policy:v1"
  , qualificationAdmissionConditionDispositions = Map.singleton
      "condition:phase1-provider:v1" (SemanticAtom "accepted")
  , qualificationAdmissionDependencyAdmissions = Set.empty
  , qualificationAdmissionSelectedArtifactRuntimeAbi = Just artifact
  , qualificationAdmissionExportedRuntimeObligations = Set.empty
  , qualificationAdmissionExportedDeploymentRequirements = Set.empty
  , qualificationAdmissionDecision = QualificationAdmitted
  }

claimRevisionOf :: ProviderReplacementSide -> QualificationClaimRevision
claimRevisionOf = deriveQualificationClaimRevision . providerReplacementClaim

proofRef :: Text -> ProviderReplacementEvidenceReference
proofRef = ProviderReplacementEvidenceReference ProofOrCertificateReference

sharedProof :: Text
sharedProof = "proof:shared-provider-law"

providerInterface :: InterfaceRevision
providerInterface = InterfaceRevision "provider.blob:v1"

providerOccurrence :: Text
providerOccurrence = "provider.requirement.blob"

instanceRevision :: InstanceRevision
instanceRevision = InstanceRevision "architecture.instance:steve:v1"

priorRealizationRevision, replacementRealizationRevision :: RealizationRevision
priorRealizationRevision = RealizationRevision "architecture.realization:steve:i1"
replacementRealizationRevision = RealizationRevision "architecture.realization:steve:i2"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
