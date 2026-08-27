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
    [ test "ARCH-010 implementations satisfy the same abstract provider interface" sameProviderInterface
    , test "ARCH-010 provider replacement preserves ArchitectureInstance" instancePreserved
    , test "ARCH-010 provider replacement changes ArchitectureRealization" realizationChanges
    , test "ARCH-010 derived replacement pair is accepted" replacementAccepts
    , test "ARCH-010 checker reports exact derived instance and realization revisions" exactDerivedRevisions
    , test "ARCH-010 replacement changes qualification/evidence/admission lineage" lineageChanges
    , test "ARCH-010 identical selected realization rebuild is deterministic" deterministicRebuild
    , test "ARCH-010 predecessor evidence cannot qualify the replacement claim" predecessorEvidenceRejects
    , test "ARCH-010 changing abstract architecture topology is not provider replacement" topologyChangeRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

sameProviderInterface :: Either String ()
sameProviderInterface = do
  assert (identityInterfaceRevision implementationOne == providerInterface)
    "implementation I1 does not refine the required interface revision"
  assert (identityInterfaceRevision implementationTwo == providerInterface)
    "implementation I2 does not refine the required interface revision"
  assert (identityDefinitionRevision implementationOne /= identityDefinitionRevision implementationTwo)
    "independent implementations collapsed to one DefinitionRevision"

instancePreserved :: Either String ()
instancePreserved = do
  let prior = providerReplacementInstanceRevision priorSide
      replacement = providerReplacementInstanceRevision replacementSide
  assert (prior == identityInstanceRevision storeInstance)
    "prior side does not name the derived ArchitectureInstance"
  assert (replacement == identityInstanceRevision storeInstance)
    "replacement side changed the abstract ArchitectureInstance"
  assert (prior == replacement)
    "provider replacement changed InstanceRevision"

realizationChanges :: Either String ()
realizationChanges = do
  assert (identityRealizationRevision priorRealization /= identityRealizationRevision replacementRealization)
    "selected implementation replacement did not revise ArchitectureRealization"
  assert (providerReplacementRealizationRevision priorSide == identityRealizationRevision priorRealization)
    "prior side does not name its derived realization"
  assert (providerReplacementRealizationRevision replacementSide == identityRealizationRevision replacementRealization)
    "replacement side does not name its derived realization"

replacementAccepts :: Either String ()
replacementAccepts = do
  result <- checked priorSide replacementSide
  assert
    (checkedProviderReplacementReusedEvidence result == Set.singleton sharedProviderContractRef)
    "shared provider-contract validity dependency was not explicitly reused"

exactDerivedRevisions :: Either String ()
exactDerivedRevisions = do
  result <- checked priorSide replacementSide
  assert (checkedProviderReplacementInstanceRevision result == identityInstanceRevision storeInstance)
    "checker did not preserve the derived InstanceRevision"
  assert (checkedProviderReplacementPriorRealizationRevision result == identityRealizationRevision priorRealization)
    "checker lost the prior derived RealizationRevision"
  assert (checkedProviderReplacementNewRealizationRevision result == identityRealizationRevision replacementRealization)
    "checker lost the replacement derived RealizationRevision"

lineageChanges :: Either String ()
lineageChanges = do
  result <- checked priorSide replacementSide
  assert (checkedProviderReplacementPriorClaimRevision result /= checkedProviderReplacementNewClaimRevision result)
    "provider qualification claim lineage was inherited"
  assert (checkedProviderReplacementPriorEvidenceRevision result /= checkedProviderReplacementNewEvidenceRevision result)
    "implementation-specific evidence lineage was inherited"
  assert (checkedProviderReplacementPriorAdmissionRevision result /= checkedProviderReplacementNewAdmissionRevision result)
    "provider admission lineage was inherited"

deterministicRebuild :: Either String ()
deterministicRebuild = do
  let rebuilt = realizationFor storeInstance implementationTwo replacementClaim replacementEvidence replacementAdmission
  assert (rebuilt == replacementRealization)
    "same exact instance and selected realization choices produced a new realization identity"

predecessorEvidenceRejects :: Either String ()
predecessorEvidenceRejects =
  let staleAdmission = admissionFor replacementClaim priorEvidence "artifact:blob:i2"
      staleSide = replacementSide
        { providerReplacementEvidence = priorEvidence
        , providerReplacementAdmission = staleAdmission
        }
  in case checkProviderReplacementQualification priorSide staleSide Map.empty of
      Left (ProviderReplacementNewIdentityError (QualificationEvidenceClaimRevisionMismatch expected actual)) -> do
        assert (expected == deriveQualificationClaimRevision replacementClaim)
          "wrong replacement claim revision in stale-evidence rejection"
        assert (actual == deriveQualificationClaimRevision priorClaim)
          "wrong predecessor claim revision in stale-evidence rejection"
      other -> Left ("predecessor evidence was accepted for replacement: " <> show other)

topologyChangeRejects :: Either String ()
topologyChangeRejects =
  let otherRealization = realizationFor otherStoreInstance implementationTwo replacementClaim replacementEvidence replacementAdmission
      otherSide = replacementSide
        { providerReplacementInstanceRevision = identityInstanceRevision otherStoreInstance
        , providerReplacementRealizationRevision = identityRealizationRevision otherRealization
        }
  in case checkProviderReplacementQualification priorSide otherSide Map.empty of
      Left (ProviderReplacementInstanceMismatch expected actual) -> do
        assert (expected == identityInstanceRevision storeInstance)
          "wrong expected InstanceRevision in topology-change rejection"
        assert (actual == identityInstanceRevision otherStoreInstance)
          "wrong actual InstanceRevision in topology-change rejection"
      other -> Left ("topology-changing replacement was accepted: " <> show other)

checked :: ProviderReplacementSide -> ProviderReplacementSide -> Either String CheckedProviderReplacementQualification
checked prior replacement =
  mapLeft show (checkProviderReplacementQualification prior replacement sharedReusePlan)

providerContractIdentity :: DeclarationIdentity
providerContractIdentity = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "BlobProvider" ["Providers"]
  , declarationKey = DeclarationKey "provider.blob.contract"
  , declarationInterfaceSemantics = providerInterfaceSemantics
  , declarationDefinitionSemantics = SemanticAtom "abstract-provider-contract"
  }

providerInterface :: InterfaceRevision
providerInterface = identityInterfaceRevision providerContractIdentity

providerInterfaceSemantics :: SemanticForm
providerInterfaceSemantics = SemanticRecord (Map.fromList
  [ ("operations", SemanticUnordered (Set.fromList
      [ SemanticAtom "read"
      , SemanticAtom "install-if-absent"
      ]))
  , ("authority", SemanticAtom "read-write")
  , ("law", SemanticAtom "no-replace:v1")
  ])

implementationOne, implementationTwo :: DeclarationIdentity
implementationOne = implementationIdentity
  (DeclarationKey "provider.blob.impl.filesystem")
  (SemanticAtom "filesystem-install-if-absent:v1")
implementationTwo = implementationIdentity
  (DeclarationKey "provider.blob.impl.object-store")
  (SemanticAtom "object-store-conditional-put:v1")

implementationIdentity :: DeclarationKey -> SemanticForm -> DeclarationIdentity
implementationIdentity key definition = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "BlobProviderImpl" ["Providers", "Internal"]
  , declarationKey = key
  , declarationInterfaceSemantics = providerInterfaceSemantics
  , declarationDefinitionSemantics = definition
  }

architectureDeclaration :: DeclarationIdentity
architectureDeclaration = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "SteveStore" ["Steve"]
  , declarationKey = DeclarationKey "architecture.steve.store"
  , declarationInterfaceSemantics = SemanticAtom "SteveStoreArchitecture:v1"
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("provider_occurrence", SemanticAtom providerOccurrence)
      , ("required_provider_interface", SemanticAtom (unInterfaceRevision providerInterface))
      ])
  }

storeInstance, otherStoreInstance :: ArchitectureInstanceIdentity
storeInstance = deriveStoreInstance (InstanceKey "steve.store")
otherStoreInstance = deriveStoreInstance (InstanceKey "steve.other-store")

deriveStoreInstance :: InstanceKey -> ArchitectureInstanceIdentity
deriveStoreInstance key = deriveArchitectureInstanceIdentity ArchitectureInstanceDescriptor
  { architectureInstanceKey = key
  , architectureParentInstanceKey = Just (InstanceKey "steve.root")
  , architectureDeclarationIdentity = architectureDeclaration
  , architectureStaticBindings = Map.fromList
      [ ("provider_occurrence", SemanticAtom providerOccurrence)
      , ("required_provider_interface", SemanticAtom (unInterfaceRevision providerInterface))
      ]
  }

priorClaim, replacementClaim :: ProviderQualificationClaimIdentityInput
priorClaim = claimFor implementationOne
replacementClaim = claimFor implementationTwo

claimFor :: DeclarationIdentity -> ProviderQualificationClaimIdentityInput
claimFor implementation = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = providerInterface
  , qualificationClaimSubject = SemanticProviderImplementation (identityDefinitionRevision implementation)
  , qualificationClaimLayer = SemanticImplementationQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "blob.read+install-if-absent")
      , ("provider-law", SemanticAtom "no-replace:v1")
      ]
  , qualificationClaimConditions = Set.singleton "condition:phase1-provider:v1"
  , qualificationClaimValidityScope = SemanticAtom "provider-validity:v1"
  }

priorEvidence, replacementEvidence :: ProviderQualificationEvidenceIdentityInput
priorEvidence = evidenceFor priorClaim "proof:blob-filesystem:v1"
replacementEvidence = evidenceFor replacementClaim "proof:blob-object-store:v1"

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
  , qualificationEvidenceValidityDependencies = Set.singleton sharedProviderContractDependency
  }

sharedProviderContractDependency :: Text
sharedProviderContractDependency = "provider-contract:v1"

sharedProviderContractRef :: ProviderReplacementEvidenceReference
sharedProviderContractRef = ProviderReplacementEvidenceReference
  { providerReplacementEvidenceReferenceKind = ValidityDependencyReference
  , providerReplacementEvidenceReferenceValue = sharedProviderContractDependency
  }

sharedProviderContractReuse :: ProviderReplacementEvidenceReuse
sharedProviderContractReuse = ProviderReplacementEvidenceReuse
  { providerReplacementReuseReference = sharedProviderContractRef
  , providerReplacementReusePriorClaimRevision = deriveQualificationClaimRevision priorClaim
  , providerReplacementReuseNewClaimRevision = deriveQualificationClaimRevision replacementClaim
  , providerReplacementReuseValidityScopeRevision =
      "validity:provider-contract-covers-both-qualified-implementations:v1"
  }

sharedReusePlan
  :: Map.Map ProviderReplacementEvidenceReference ProviderReplacementEvidenceReuse
sharedReusePlan = Map.singleton sharedProviderContractRef sharedProviderContractReuse

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
  , qualificationAdmissionRequiredInterface = providerInterface
  , qualificationAdmissionRealizationContextRevision = "steve.realization-context:v1"
  , qualificationAdmissionAssurancePolicyRevision = "steve.assurance-policy:v1"
  , qualificationAdmissionConditionDispositions = Map.singleton
      "condition:phase1-provider:v1" (SemanticAtom "accepted")
  , qualificationAdmissionDependencyAdmissions = Set.empty
  , qualificationAdmissionSelectedArtifactRuntimeAbi = Just artifact
  , qualificationAdmissionExportedRuntimeObligations = Set.empty
  , qualificationAdmissionExportedDeploymentRequirements = Set.empty
  , qualificationAdmissionDecision = QualificationAdmitted
  }

priorRealization, replacementRealization :: ArchitectureRealizationIdentity
priorRealization = realizationFor storeInstance implementationOne priorClaim priorEvidence priorAdmission
replacementRealization = realizationFor storeInstance implementationTwo replacementClaim replacementEvidence replacementAdmission

realizationFor
  :: ArchitectureInstanceIdentity
  -> DeclarationIdentity
  -> ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> ProviderQualificationAdmissionIdentityInput
  -> ArchitectureRealizationIdentity
realizationFor instanceIdentity implementation claim evidence admission =
  deriveArchitectureRealizationIdentity ArchitectureRealizationDescriptor
    { realizationInstanceIdentity = instanceIdentity
    , realizationSemantics = SemanticRecord (Map.fromList
        [ ("provider_occurrence", SemanticAtom providerOccurrence)
        , ("required_interface", SemanticAtom (unInterfaceRevision providerInterface))
        , ("selected_implementation", SemanticAtom
            (unDefinitionRevision (identityDefinitionRevision implementation)))
        , ("qualification_claim", SemanticAtom
            (unQualificationClaimRevision (deriveQualificationClaimRevision claim)))
        , ("qualification_evidence", SemanticAtom
            (unQualificationEvidenceRevision (deriveQualificationEvidenceRevision evidence)))
        , ("qualification_admission", SemanticAtom
            (unQualificationAdmissionRevision (deriveQualificationAdmissionRevision admission)))
        , ("selected_artifact", SemanticAtom
            (maybe "" id (qualificationAdmissionSelectedArtifactRuntimeAbi admission)))
        ])
    }

priorSide, replacementSide :: ProviderReplacementSide
priorSide = sideFor storeInstance priorRealization priorClaim priorEvidence priorAdmission
replacementSide = sideFor storeInstance replacementRealization replacementClaim replacementEvidence replacementAdmission

sideFor
  :: ArchitectureInstanceIdentity
  -> ArchitectureRealizationIdentity
  -> ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> ProviderQualificationAdmissionIdentityInput
  -> ProviderReplacementSide
sideFor instanceIdentity realization claim evidence admission = ProviderReplacementSide
  { providerReplacementClaim = claim
  , providerReplacementEvidence = evidence
  , providerReplacementAdmission = admission
  , providerReplacementInstanceRevision = identityInstanceRevision instanceIdentity
  , providerReplacementRealizationRevision = identityRealizationRevision realization
  }

providerOccurrence :: Text
providerOccurrence = "provider.requirement.blob"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
