{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.ProviderCallWitnesses
  ( uploadProviderCallStageBundle
  , steveProviderCallStageBundle
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.ProviderQualification
  ( CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderContract (..)
  , ProviderImplementation (..)
  , ProviderImplementationEntryKey (..)
  , ProviderOperationKey (..)
  )
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationAdmissionDecision (..)
  , ProviderQualificationAdmissionIdentityInput (..)
  , ProviderQualificationClaimIdentityInput (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , ProviderQualificationLayer (..)
  , ProviderQualificationSubject (..)
  , checkQualificationAdmissionIdentity
  , deriveQualificationClaimRevision
  , deriveQualificationEvidenceRevision
  )
import Phil.Core.Static
  ( InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Examples.Phase1.SubjectWitnesses
  ( steveSubjectStageBundle
  , uploadSubjectStageBundle
  )
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualificationArtifact (..)
  , SteveProviderQualificationError (..)
  , SteveProviderQualifications (..)
  , materializeSteveProviderQualifications
  )
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import Phil.Systems.ProviderCallCorrespondence

uploadProviderCallStageBundle :: Either String ProviderCallStageBundle
uploadProviderCallStageBundle = do
  selection <- uploadStorageSelection
  link <- exactLink
    uploadStoreMechanism selection (ProviderOperationKey "upload.store")
    "phase0.runtime.store" "owned-payload->upload-id-or-storage-failure"
  pure (makeProviderCallStageBundle
    uploadSubjectStageBundle
    (Map.singleton (selectedProviderOccurrence selection) selection)
    (Set.singleton uploadStoreMechanism)
    (Map.singleton uploadStoreMechanism link))

steveProviderCallStageBundle :: Either String ProviderCallStageBundle
steveProviderCallStageBundle = do
  base <- steveSubjectStageBundle
  qualifications <- mapLeft (Text.unpack . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  let digestSelection = selectionFromSteveArtifact
        (steveDigestProviderQualification qualifications)
      blobSelection = selectionFromSteveArtifact
        (steveBlobProviderQualification qualifications)
      selections = Map.fromList
        [ (selectedProviderOccurrence digestSelection, digestSelection)
        , (selectedProviderOccurrence blobSelection, blobSelection)
        ]
  digestCompute <- exactLink steveDigestComputeMechanism digestSelection
    (ProviderOperationKey "digest.compute")
    "sha256_compute" "borrowed-bytes->content-id+proof"
  blobInstall <- exactLink steveBlobInstallMechanism blobSelection
    (ProviderOperationKey "blob.install-if-absent")
    "blob_install_if_absent" "content-id+borrowed-bytes->install-status"
  blobRead <- exactLink steveBlobReadMechanism blobSelection
    (ProviderOperationKey "blob.read")
    "blob_read" "content-id->owned-bytes-or-read-error"
  digestCheck <- exactLink steveDigestCheckMechanism digestSelection
    (ProviderOperationKey "digest.check")
    "sha256_check" "content-id+borrowed-bytes->digest-check"
  let links = Map.fromList
        [ (steveDigestComputeMechanism, digestCompute)
        , (steveBlobInstallMechanism, blobInstall)
        , (steveBlobReadMechanism, blobRead)
        , (steveDigestCheckMechanism, digestCheck)
        ]
  pure (makeProviderCallStageBundle
    base selections (Map.keysSet links) links)

selectionFromSteveArtifact
  :: SteveProviderQualificationArtifact
  -> SelectedProviderAdmission
selectionFromSteveArtifact artifact = SelectedProviderAdmission
  { selectedProviderOccurrence =
      qualificationAdmissionProviderOccurrence (steveProviderIdentityAdmission artifact)
  , selectedProviderRequiredInterface =
      providerContractInterfaceRevision (steveProviderContract artifact)
  , selectedProviderSubject =
      qualificationClaimSubject (steveProviderIdentityClaim artifact)
  , selectedProviderClaimInput = steveProviderIdentityClaim artifact
  , selectedProviderAdmissionInput = steveProviderIdentityAdmission artifact
  , selectedProviderCheckedAdmission = steveProviderCheckedAdmission artifact
  , selectedProviderOperationEntries = Map.map
      checkedProviderImplementationEntry
      (checkedProviderOperations (steveProviderCheckedSemantic artifact))
  , selectedProviderRuntimeSymbols =
      providerImplementationSymbols (steveProviderImplementation artifact)
  }

uploadStorageSelection :: Either String SelectedProviderAdmission
uploadStorageSelection = do
  checked <- mapLeft show $ checkQualificationAdmissionIdentity
    uploadStorageClaim uploadStorageEvidence uploadStorageAdmission
  pure SelectedProviderAdmission
    { selectedProviderOccurrence = "upload.storage-provider"
    , selectedProviderRequiredInterface = uploadStorageInterface
    , selectedProviderSubject = OpaqueProviderBoundary "phase0.upload.storage.runtime-boundary"
    , selectedProviderClaimInput = uploadStorageClaim
    , selectedProviderAdmissionInput = uploadStorageAdmission
    , selectedProviderCheckedAdmission = checked
    , selectedProviderOperationEntries = Map.singleton
        (ProviderOperationKey "upload.store")
        (ProviderImplementationEntryKey "phase0.runtime.store")
    , selectedProviderRuntimeSymbols = Set.singleton "phase0.runtime.store"
    }

uploadStorageInterface :: InterfaceRevision
uploadStorageInterface = InterfaceRevision "upload.provider.storage.v1"

uploadStorageClaim :: ProviderQualificationClaimIdentityInput
uploadStorageClaim = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = uploadStorageInterface
  , qualificationClaimSubject = OpaqueProviderBoundary
      "phase0.upload.storage.runtime-boundary"
  , qualificationClaimLayer = CollapsedOpaqueQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operation.upload.store", SemanticAtom
          "exact Phase-0 StorageBoundary success/failure operation")
      , ("runtime-assurance", SemanticAtom
          "evidence.upload.storage.runtime")
      ]
  , qualificationClaimConditions = Set.empty
  , qualificationClaimValidityScope = SemanticAtom
      "phase0.upload.storage-success.boundary.v1"
  }

uploadStorageEvidence :: ProviderQualificationEvidenceIdentityInput
uploadStorageEvidence = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision uploadStorageClaim
  , qualificationEvidenceObligationDispositions = Map.singleton
      "storage.success"
      (SemanticAtom "runtime-enforced:evidence.upload.storage.runtime")
  , qualificationEvidenceRefs = Set.singleton "evidence.upload.storage.runtime"
  , qualificationEvidenceProofRefs = Set.empty
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs =
      Set.singleton "evidence.upload.storage.runtime"
  , qualificationEvidenceAssumptionRefs = Set.empty
  , qualificationEvidenceValidityDependencies =
      Set.singleton "upload.accepted.storage_success"
  }

uploadStorageAdmission :: ProviderQualificationAdmissionIdentityInput
uploadStorageAdmission = ProviderQualificationAdmissionIdentityInput
  { qualificationAdmissionClaimRevision = deriveQualificationClaimRevision uploadStorageClaim
  , qualificationAdmissionEvidenceRevision =
      deriveQualificationEvidenceRevision uploadStorageEvidence
  , qualificationAdmissionProviderOccurrence = "upload.storage-provider"
  , qualificationAdmissionRequiredInterface = uploadStorageInterface
  , qualificationAdmissionRealizationContextRevision =
      "phase1.upload.realization.host.v1"
  , qualificationAdmissionAssurancePolicyRevision =
      "phase1.upload.phase0-storage-bridge-policy.v1"
  , qualificationAdmissionConditionDispositions = Map.empty
  , qualificationAdmissionDependencyAdmissions = Set.empty
  , qualificationAdmissionSelectedArtifactRuntimeAbi =
      Just "phase0.systems.storage-boundary.v1"
  , qualificationAdmissionExportedRuntimeObligations = Set.empty
  , qualificationAdmissionExportedDeploymentRequirements = Set.empty
  , qualificationAdmissionDecision = QualificationAdmitted
  }

exactLink
  :: SystemsMechanismKey
  -> SelectedProviderAdmission
  -> ProviderOperationKey
  -> Text
  -> Text
  -> Either String ProviderCallLink
exactLink mechanism selection operation symbol signature = do
  entry <- maybe
    (Left ("selected provider lacks operation: " <> show operation))
    Right
    (Map.lookup operation (selectedProviderOperationEntries selection))
  pure ProviderCallLink
    { providerCallMechanism = mechanism
    , providerCallBindingBasis = ExactProviderCallBinding
        (selectedProviderOccurrence selection)
        (checkedQualificationAdmissionRevision
          (selectedProviderCheckedAdmission selection))
        (selectedProviderRequiredInterface selection)
        operation
        entry
    , providerCallRuntimeSymbol = symbol
    , providerCallRuntimeSignature = signature
    }

uploadStoreMechanism :: SystemsMechanismKey
uploadStoreMechanism = SystemsMechanismKey
  "UploadServer:server.store:term.store"

steveDigestComputeMechanism, steveBlobInstallMechanism :: SystemsMechanismKey
steveBlobReadMechanism, steveDigestCheckMechanism :: SystemsMechanismKey
steveDigestComputeMechanism = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"
steveBlobInstallMechanism = SystemsMechanismKey
  "StevePut:put.install:term.runtime-choice.BlobProvider.install-if-absent"
steveBlobReadMechanism = SystemsMechanismKey
  "SteveGet:get.entry:term.runtime-choice.BlobProvider.read"
steveDigestCheckMechanism = SystemsMechanismKey
  "SteveGet:get.check:term.runtime-choice.DigestProvider.check"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
