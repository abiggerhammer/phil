{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderReplacementQualification
import Phil.Core.Static
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-015 independently qualified replacement accepts" independentReplacementAccepted
    , test "PROV-015 replacement preserves abstract occurrence and instance" abstractBindingPreserved
    , test "PROV-015 replacement changes qualification and realization lineage" lineageChanges
    , test "PROV-015 inherited evidence reference without scope rejects" inheritedEvidenceRejected
    , test "PROV-015 reusable evidence with independent validity scope accepts" explicitReusableEvidenceAccepted
    , test "PROV-015 reusable evidence requires nonempty validity scope" emptyReuseScopeRejected
    , test "PROV-015 same implementation subject is not replacement" sameSubjectRejected
    , test "PROV-015 public interface must remain fixed" interfaceMismatchRejected
    , test "PROV-015 abstract provider occurrence must remain fixed" occurrenceMismatchRejected
    , test "PROV-015 ArchitectureInstance must remain fixed" instanceMismatchRejected
    , test "PROV-015 RealizationRevision must change" unchangedRealizationRejected
    , test "PROV-015 replacement evidence must bind replacement claim" predecessorEvidenceBundleRejected
    , test "PROV-015 replacement admission is independently checked" predecessorAdmissionRejected
    , test "PROV-015 rejected replacement admission cannot be selected" rejectedReplacementRejected
    , test "PROV-015 semantic implementation may be replaced by collapsed opaque qualification" crossLayerReplacementAccepted
    , test "PROV-015 reuse justification cannot name unshared evidence" unexpectedReuseRejected
    , test "PROV-015 reuse justification binds exact replacement claim" reuseClaimMismatchRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

independentReplacementAccepted :: Either String ()
independentReplacementAccepted = do
  _ <- mapLeft show $ checkProviderReplacementQualification
    priorSide replacementSide Map.empty
  Right ()

abstractBindingPreserved :: Either String ()
abstractBindingPreserved = do
  checked <- mapLeft show $ checkProviderReplacementQualification
    priorSide replacementSide Map.empty
  assert (checkedProviderReplacementRequiredInterface checked == providerInterface)
    "replacement changed public provider interface"
  assert (checkedProviderReplacementOccurrence checked == providerOccurrence)
    "replacement changed abstract provider occurrence"
  assert (checkedProviderReplacementInstanceRevision checked == instanceRevision)
    "replacement changed ArchitectureInstance"

lineageChanges :: Either String ()
lineageChanges = do
  checked <- mapLeft show $ checkProviderReplacementQualification
    priorSide replacementSide Map.empty
  assert (checkedProviderReplacementPriorClaimRevision checked /=
          checkedProviderReplacementNewClaimRevision checked)
    "replacement inherited claim revision"
  assert (checkedProviderReplacementPriorEvidenceRevision checked /=
          checkedProviderReplacementNewEvidenceRevision checked)
    "replacement inherited evidence revision"
  assert (checkedProviderReplacementPriorAdmissionRevision checked /=
          checkedProviderReplacementNewAdmissionRevision checked)
    "replacement inherited admission revision"
  assert (checkedProviderReplacementPriorRealizationRevision checked /=
          checkedProviderReplacementNewRealizationRevision checked)
    "replacement failed to revise ArchitectureRealization"

inheritedEvidenceRejected :: Either String ()
inheritedEvidenceRejected = do
  let sharedPrior = sideWithProof priorSide "proof:shared-provider-law"
      sharedNew = sideWithProof replacementSide "proof:shared-provider-law"
      expectedRef = ProviderReplacementEvidenceReference
        ProofOrCertificateReference "proof:shared-provider-law"
  case checkProviderReplacementQualification sharedPrior sharedNew Map.empty of
    Left (ProviderReplacementSharedEvidenceWithoutScope refs) ->
      assert (refs == Set.singleton expectedRef) "wrong inherited-evidence diagnostic"
    other -> Left ("inherited evidence shortcut was accepted: " <> show other)

explicitReusableEvidenceAccepted :: Either String ()
explicitReusableEvidenceAccepted = do
  let sharedPrior = sideWithProof priorSide "proof:shared-provider-law"
      sharedNew = sideWithProof replacementSide "proof:shared-provider-law"
      ref = ProviderReplacementEvidenceReference
        ProofOrCertificateReference "proof:shared-provider-law"
      plan = Map.singleton ref ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = sideClaimRevision sharedPrior
        , providerReplacementReuseNewClaimRevision = sideClaimRevision sharedNew
        , providerReplacementReuseValidityScopeRevision =
            "validity:proof-covers-both-implementations:v1"
        }
  checked <- mapLeft show $ checkProviderReplacementQualification
    sharedPrior sharedNew plan
  assert (checkedProviderReplacementReusedEvidence checked == Set.singleton ref)
    "explicit reusable evidence was not retained"

emptyReuseScopeRejected :: Either String ()
emptyReuseScopeRejected = do
  let sharedPrior = sideWithProof priorSide "proof:shared-provider-law"
      sharedNew = sideWithProof replacementSide "proof:shared-provider-law"
      ref = ProviderReplacementEvidenceReference
        ProofOrCertificateReference "proof:shared-provider-law"
      plan = Map.singleton ref ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = sideClaimRevision sharedPrior
        , providerReplacementReuseNewClaimRevision = sideClaimRevision sharedNew
        , providerReplacementReuseValidityScopeRevision = ""
        }
  case checkProviderReplacementQualification sharedPrior sharedNew plan of
    Left (ProviderReplacementReuseScopeMissing actual) ->
      assert (actual == ref) "wrong reuse-scope diagnostic"
    other -> Left ("empty evidence reuse scope was accepted: " <> show other)

sameSubjectRejected :: Either String ()
sameSubjectRejected = do
  let sameClaim = priorClaim
      sameEvidence = evidenceFor sameClaim "proof:second-bundle"
      sameAdmission = admissionFor sameClaim sameEvidence "artifact:i1-second"
      same = replacementSide
        { providerReplacementClaim = sameClaim
        , providerReplacementEvidence = sameEvidence
        , providerReplacementAdmission = sameAdmission
        }
  case checkProviderReplacementQualification priorSide same Map.empty of
    Left (ProviderReplacementSameImplementationSubject subject) ->
      assert (subject == qualificationClaimSubject priorClaim) "wrong same-subject diagnostic"
    other -> Left ("same implementation was treated as replacement: " <> show other)

interfaceMismatchRejected :: Either String ()
interfaceMismatchRejected = do
  let wrongClaim = replacementClaim
        { qualificationClaimRequiredInterface = InterfaceRevision "provider.blob:v2" }
      wrongEvidence = evidenceFor wrongClaim "proof:i2-v2"
      wrongAdmission = admissionFor wrongClaim wrongEvidence "artifact:i2-v2"
      wrong = replacementSide
        { providerReplacementClaim = wrongClaim
        , providerReplacementEvidence = wrongEvidence
        , providerReplacementAdmission = wrongAdmission
        }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementInterfaceMismatch expected actual) -> do
      assert (expected == providerInterface) "wrong expected interface"
      assert (actual == InterfaceRevision "provider.blob:v2") "wrong replacement interface"
    other -> Left ("interface-changing replacement was accepted: " <> show other)

occurrenceMismatchRejected :: Either String ()
occurrenceMismatchRejected = do
  let admission = providerReplacementAdmission replacementSide
      wrongAdmission = admission
        { qualificationAdmissionProviderOccurrence = "provider.requirement.other" }
      wrong = replacementSide { providerReplacementAdmission = wrongAdmission }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementOccurrenceMismatch expected actual) -> do
      assert (expected == providerOccurrence) "wrong expected occurrence"
      assert (actual == "provider.requirement.other") "wrong replacement occurrence"
    other -> Left ("occurrence-changing replacement was accepted: " <> show other)

instanceMismatchRejected :: Either String ()
instanceMismatchRejected = do
  let otherInstance = InstanceRevision "architecture.instance:other"
      wrong = replacementSide { providerReplacementInstanceRevision = otherInstance }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementInstanceMismatch expected actual) -> do
      assert (expected == instanceRevision) "wrong expected instance"
      assert (actual == otherInstance) "wrong replacement instance"
    other -> Left ("instance-changing replacement was accepted: " <> show other)

unchangedRealizationRejected :: Either String ()
unchangedRealizationRejected = do
  let wrong = replacementSide
        { providerReplacementRealizationRevision =
            providerReplacementRealizationRevision priorSide }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementRealizationUnchanged revision) ->
      assert (revision == priorRealizationRevision) "wrong unchanged realization"
    other -> Left ("replacement reused realization revision: " <> show other)

predecessorEvidenceBundleRejected :: Either String ()
predecessorEvidenceBundleRejected = do
  let wrong = replacementSide
        { providerReplacementEvidence = providerReplacementEvidence priorSide }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementNewIdentityError
      (QualificationEvidenceClaimRevisionMismatch _ actual)) ->
        assert (actual == sideClaimRevision priorSide) "wrong inherited evidence claim"
    other -> Left ("predecessor evidence bundle was accepted for replacement: " <> show other)

predecessorAdmissionRejected :: Either String ()
predecessorAdmissionRejected = do
  let wrong = replacementSide
        { providerReplacementAdmission = providerReplacementAdmission priorSide }
  case checkProviderReplacementQualification priorSide wrong Map.empty of
    Left (ProviderReplacementNewIdentityError _) -> Right ()
    other -> Left ("predecessor admission was accepted for replacement: " <> show other)

rejectedReplacementRejected :: Either String ()
rejectedReplacementRejected = do
  let admission = providerReplacementAdmission replacementSide
      rejected = replacementSide
        { providerReplacementAdmission = admission
            { qualificationAdmissionDecision =
                QualificationRejected (Set.singleton "policy-rejected") }
        }
  case checkProviderReplacementQualification priorSide rejected Map.empty of
    Left (ProviderReplacementNewAdmissionRejected reasons) ->
      assert (reasons == Set.singleton "policy-rejected") "wrong rejection reasons"
    other -> Left ("rejected replacement admission was accepted: " <> show other)

crossLayerReplacementAccepted :: Either String ()
crossLayerReplacementAccepted = do
  let opaqueClaim = claimFor
        (OpaqueProviderBoundary "opaque-service:blob:v1")
        CollapsedOpaqueQualification
      opaqueEvidence = evidenceFor opaqueClaim "evidence:opaque-blob:v1"
      opaqueAdmission = admissionFor opaqueClaim opaqueEvidence "opaque-service:blob:v1"
      opaqueSide = replacementSide
        { providerReplacementClaim = opaqueClaim
        , providerReplacementEvidence = opaqueEvidence
        , providerReplacementAdmission = opaqueAdmission
        }
  _ <- mapLeft show $ checkProviderReplacementQualification
    priorSide opaqueSide Map.empty
  Right ()

unexpectedReuseRejected :: Either String ()
unexpectedReuseRejected = do
  let ref = ProviderReplacementEvidenceReference
        ProofOrCertificateReference "proof:not-shared"
      plan = Map.singleton ref ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = sideClaimRevision priorSide
        , providerReplacementReuseNewClaimRevision = sideClaimRevision replacementSide
        , providerReplacementReuseValidityScopeRevision = "validity:v1"
        }
  case checkProviderReplacementQualification priorSide replacementSide plan of
    Left (ProviderReplacementUnexpectedReuseJustification refs) ->
      assert (refs == Set.singleton ref) "wrong unexpected-reuse diagnostic"
    other -> Left ("reuse justification for unshared evidence was accepted: " <> show other)

reuseClaimMismatchRejected :: Either String ()
reuseClaimMismatchRejected = do
  let sharedPrior = sideWithProof priorSide "proof:shared-provider-law"
      sharedNew = sideWithProof replacementSide "proof:shared-provider-law"
      ref = ProviderReplacementEvidenceReference
        ProofOrCertificateReference "proof:shared-provider-law"
      wrongClaim = QualificationClaimRevision "claim:wrong"
      plan = Map.singleton ref ProviderReplacementEvidenceReuse
        { providerReplacementReuseReference = ref
        , providerReplacementReusePriorClaimRevision = sideClaimRevision sharedPrior
        , providerReplacementReuseNewClaimRevision = wrongClaim
        , providerReplacementReuseValidityScopeRevision = "validity:v1"
        }
  case checkProviderReplacementQualification sharedPrior sharedNew plan of
    Left (ProviderReplacementReuseNewClaimMismatch expected actual) -> do
      assert (expected == sideClaimRevision sharedNew) "wrong expected replacement claim"
      assert (actual == wrongClaim) "wrong reuse replacement claim"
    other -> Left ("reuse justification with wrong claim was accepted: " <> show other)

priorSide, replacementSide :: ProviderReplacementSide
priorSide = ProviderReplacementSide
  { providerReplacementClaim = priorClaim
  , providerReplacementEvidence = priorEvidence
  , providerReplacementAdmission = priorAdmission
  , providerReplacementInstanceRevision = instanceRevision
  , providerReplacementRealizationRevision = priorRealizationRevision
  }
replacementSide = ProviderReplacementSide
  { providerReplacementClaim = replacementClaim
  , providerReplacementEvidence = replacementEvidence
  , providerReplacementAdmission = replacementAdmission
  , providerReplacementInstanceRevision = instanceRevision
  , providerReplacementRealizationRevision = replacementRealizationRevision
  }

priorClaim, replacementClaim :: ProviderQualificationClaimIdentityInput
priorClaim = claimFor
  (SemanticProviderImplementation (DefinitionRevision "provider.blob.impl:i1"))
  SemanticImplementationQualification
replacementClaim = claimFor
  (SemanticProviderImplementation (DefinitionRevision "provider.blob.impl:i2"))
  SemanticImplementationQualification

claimFor
  :: ProviderQualificationSubject
  -> ProviderQualificationLayer
  -> ProviderQualificationClaimIdentityInput
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

priorEvidence, replacementEvidence :: ProviderQualificationEvidenceIdentityInput
priorEvidence = evidenceFor priorClaim "proof:i1-provider-law"
replacementEvidence = evidenceFor replacementClaim "proof:i2-provider-law"

evidenceFor
  :: ProviderQualificationClaimIdentityInput
  -> Text
  -> ProviderQualificationEvidenceIdentityInput
evidenceFor claim proofRef = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision claim
  , qualificationEvidenceObligationDispositions = Map.fromList
      [ ("provider-law.no-replace", SemanticAtom "discharged-by-evidence") ]
  , qualificationEvidenceRefs = Set.empty
  , qualificationEvidenceProofRefs = Set.singleton proofRef
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs = Set.empty
  , qualificationEvidenceAssumptionRefs = Set.empty
  , qualificationEvidenceValidityDependencies = Set.singleton "validity:provider-law:v1"
  }

priorAdmission, replacementAdmission :: ProviderQualificationAdmissionIdentityInput
priorAdmission = admissionFor priorClaim priorEvidence "artifact:blob:i1"
replacementAdmission = admissionFor replacementClaim replacementEvidence "artifact:blob:i2"

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
  , qualificationAdmissionConditionDispositions = Map.fromList
      [ ("condition:phase1-provider:v1", SemanticAtom "accepted") ]
  , qualificationAdmissionDependencyAdmissions = Set.empty
  , qualificationAdmissionSelectedArtifactRuntimeAbi = Just artifact
  , qualificationAdmissionExportedRuntimeObligations = Set.empty
  , qualificationAdmissionExportedDeploymentRequirements = Set.empty
  , qualificationAdmissionDecision = QualificationAdmitted
  }

sideWithProof :: ProviderReplacementSide -> Text -> ProviderReplacementSide
sideWithProof side proofRef =
  let claim = providerReplacementClaim side
      evidence = evidenceFor claim proofRef
      admission = admissionFor claim evidence
        (case qualificationAdmissionSelectedArtifactRuntimeAbi
          (providerReplacementAdmission side) of
          Just artifact -> artifact
          Nothing -> "artifact:missing")
  in side
      { providerReplacementEvidence = evidence
      , providerReplacementAdmission = admission
      }

sideClaimRevision :: ProviderReplacementSide -> QualificationClaimRevision
sideClaimRevision = deriveQualificationClaimRevision . providerReplacementClaim

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
