{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualifications (..)
  , SteveProviderQualificationArtifact (..)
  , SteveProviderQualificationError (..)
  , materializeSteveProviderQualifications
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityOperationKey (..)
  , AuthoritySubjectKey (..)
  )
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  , CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.CallableScope (LoanScopeKey (..))
import Phil.Core.ProviderAuthorityQualification
import Phil.Core.ProviderEvidenceQualification
import Phil.Core.ProviderLawQualification
import Phil.Core.ProviderLifecycleQualification
import Phil.Core.ProviderQualification
import Phil.Core.ProviderQualificationIdentity
import Phil.Core.ProviderStateQualification
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax
  ( Outcome (..)
  , RefSort (..)
  , RefTerm (..)
  )
import qualified SteveProviderQualificationWitnessKernel as WitnessKernel

-- | The two concrete Phase 1 Steve provider qualification artifacts. Both use
-- the same generic representation; their differences are only provider-specific
-- contracts, checked relations, evidence, and conditions.
data SteveProviderQualifications = SteveProviderQualifications
  { steveDigestProviderQualification :: SteveProviderQualificationArtifact
  , steveBlobProviderQualification :: SteveProviderQualificationArtifact
  }
  deriving (Eq, Ord, Show)

data SteveProviderQualificationArtifact = SteveProviderQualificationArtifact
  { steveProviderLabel :: Text
  , steveProviderContract :: ProviderContract
  , steveProviderImplementation :: ProviderImplementation
  , steveProviderSemanticClaim :: ProviderQualificationClaim
  , steveProviderCheckedSemantic :: CheckedProviderSemanticQualification
  , steveProviderStateRefinement :: Maybe ProviderStateRefinement
  , steveProviderCheckedState :: Maybe CheckedProviderStateQualification
  , steveProviderLaws :: [(ProviderLaw, CheckedProviderLawCorpus)]
  , steveProviderLifecycleContract :: Maybe ProviderLifecycleContract
  , steveProviderLifecycleModel :: Maybe ProviderLifecycleModel
  , steveProviderCheckedLifecycle :: Maybe CheckedProviderLifecycleQualification
  , steveProviderEvidenceCompetences :: [CheckedProviderEvidenceProducerCompetence]
  , steveProviderAuthoritySpec :: ProviderAuthorityQualificationSpec
  , steveProviderCheckedAuthority :: CheckedProviderAuthorityQualification
  , steveProviderIdentityClaim :: ProviderQualificationClaimIdentityInput
  , steveProviderIdentityEvidence :: ProviderQualificationEvidenceIdentityInput
  , steveProviderIdentityAdmission :: ProviderQualificationAdmissionIdentityInput
  , steveProviderCheckedAdmission :: CheckedProviderQualificationAdmissionIdentity
  , steveProviderRequiredObligationKeys :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

newtype SteveProviderQualificationError = SteveProviderQualificationError
  { unSteveProviderQualificationError :: Text
  }
  deriving (Eq, Ord, Show)

materializeSteveProviderQualifications
  :: Either SteveProviderQualificationError SteveProviderQualifications
materializeSteveProviderQualifications = do
  digest <- materializeDigestProvider
  blob <- materializeBlobProvider
  let qualifications = SteveProviderQualifications
        { steveDigestProviderQualification = digest
        , steveBlobProviderQualification = blob
        }
  if steveProviderQualificationWitnessKernelAccepts qualifications
    then pure qualifications
    else Left (SteveProviderQualificationError
      "Steve provider witness certified-kernel disagreement")

steveProviderQualificationWitnessKernelAccepts
  :: SteveProviderQualifications
  -> Bool
steveProviderQualificationWitnessKernelAccepts qualifications =
  WitnessKernel.decideSteveProviderQualificationWitnessByFacts
    (admissionAccepted digest && admissionAccepted blob)
    (digestSubjectExactFact digest)
    (digestObservationMappedFact digest)
    (digestBorrowPreservedFact digest)
    (blobBorrowAllOutcomesFact blob)
    (blobWholeLayersPresentFact blob)
    (blobNoReplaceEnforcedFact blob)
    (blobPartialPublicationForbiddenFact blob)
    (blobAuthorityDispositionedFact blob)
    (obligationManifestExactFact digest && obligationManifestExactFact blob)
    (conditionLineageExactFact digest && conditionLineageExactFact blob
      && digestSha256ConditionExplicitFact digest)
  where
    digest = steveDigestProviderQualification qualifications
    blob = steveBlobProviderQualification qualifications

admissionAccepted :: SteveProviderQualificationArtifact -> Bool
admissionAccepted artifact = case checkedQualificationAdmissionDecision
    (steveProviderCheckedAdmission artifact) of
  QualificationAdmitted -> True
  QualificationRejected _ -> False

digestSubjectExactFact :: SteveProviderQualificationArtifact -> Bool
digestSubjectExactFact artifact = case steveProviderEvidenceCompetences artifact of
  competence : _ ->
    checkedProviderEvidenceSubject competence == digestComputeSubject
  [] -> False

digestObservationMappedFact :: SteveProviderQualificationArtifact -> Bool
digestObservationMappedFact artifact = case steveProviderEvidenceCompetences artifact of
  competence : _ -> case checkedProviderEvidenceObservation competence of
    ScopedBorrowEvidenceObservation _ _ ->
      case checkedProviderEvidenceMapping competence of
        CheckedObservationToStableSubject _ observation subject ->
          observation == checkedProviderEvidenceObservation competence
            && subject == checkedProviderEvidenceSubject competence
        _ -> False
    _ -> False
  [] -> False

digestBorrowPreservedFact :: SteveProviderQualificationArtifact -> Bool
digestBorrowPreservedFact artifact = case Map.lookup digestComputeOperation
    (providerContractOperations (steveProviderContract artifact)) of
  Just operation -> case Map.elems (providerOperationOutcomeResidues operation) of
    [residue] -> resourceBorrowPreserved digestCandidateResource residue
    _ -> False
  Nothing -> False

blobBorrowAllOutcomesFact :: SteveProviderQualificationArtifact -> Bool
blobBorrowAllOutcomesFact artifact = case Map.lookup blobInstallOperation
    (providerContractOperations (steveProviderContract artifact)) of
  Just operation ->
    let residues = Map.elems (providerOperationOutcomeResidues operation)
    in length residues == 3
      && all (resourceBorrowPreserved blobCandidateResource) residues
  Nothing -> False

resourceBorrowPreserved :: ProviderResourceKey -> ProviderResourceResidue -> Bool
resourceBorrowPreserved key residue =
  Set.member key (providerResidueBorrowedInputs residue)
    && not (Set.member key (providerResidueConsumedInputs residue))

blobWholeLayersPresentFact :: SteveProviderQualificationArtifact -> Bool
blobWholeLayersPresentFact artifact =
  maybe False (const True) (steveProviderCheckedState artifact)
    && not (null (steveProviderLaws artifact))
    && maybe False (const True) (steveProviderCheckedLifecycle artifact)
    && not (Set.null (checkedProviderAuthorityExtra
      (steveProviderCheckedAuthority artifact)))

blobNoReplaceEnforcedFact :: SteveProviderQualificationArtifact -> Bool
blobNoReplaceEnforcedFact artifact = case steveProviderLaws artifact of
  (law, _) : _ ->
    let installed = ProviderImplementationEvent
          blobInstallOperation blobImplInstallInstalled
    in case checkProviderLawTrace
        (steveProviderCheckedSemantic artifact) law [installed, installed] of
      Left (ProviderLawViolation _ 1 _ _) -> True
      _ -> False
  [] -> False

blobPartialPublicationForbiddenFact
  :: SteveProviderQualificationArtifact
  -> Bool
blobPartialPublicationForbiddenFact artifact =
  case (steveProviderLifecycleContract artifact, steveProviderLifecycleModel artifact) of
    (Just contract, Just model) ->
      let partialState = ProviderObservableStateKey "object.partially-committed"
          partial = ProviderInterruptionObservation
            blobObservationBoundary
            partialState
            emptyResidue
            ProviderRetrySameOperation
          broken = ProviderLifecycleModel $ Map.insert
            blobAfterPublicationPoint
            (Set.singleton partial)
            (providerLifecycleImplementationObservations model)
      in case checkProviderLifecycleQualification
          (steveProviderCheckedSemantic artifact) contract broken of
        Left (ProviderLifecycleForbiddenObservableState point state) ->
          point == blobAfterPublicationPoint && state == partialState
        _ -> False
    _ -> False

blobAuthorityDispositionedFact :: SteveProviderQualificationArtifact -> Bool
blobAuthorityDispositionedFact artifact =
  checkedProviderAuthorityExtra checked == expectedExtra
    && Map.lookup blobAuthorityOverwrite dispositions
      == Just (ExtraAuthorityAssumptionDependent blobConfinementAssumption)
    && Map.lookup blobAuthorityDelete dispositions
      == Just (ExtraAuthorityAssumptionDependent blobConfinementAssumption)
  where
    checked = steveProviderCheckedAuthority artifact
    dispositions = checkedProviderAuthorityDispositions checked
    expectedExtra = Set.fromList [blobAuthorityOverwrite, blobAuthorityDelete]

obligationManifestExactFact :: SteveProviderQualificationArtifact -> Bool
obligationManifestExactFact artifact =
  Map.keysSet (qualificationEvidenceObligationDispositions
    (steveProviderIdentityEvidence artifact))
    == steveProviderRequiredObligationKeys artifact

conditionLineageExactFact :: SteveProviderQualificationArtifact -> Bool
conditionLineageExactFact artifact =
  conditions == evidenceAssumptions && conditions == admissionConditions
  where
    conditions = qualificationClaimConditions (steveProviderIdentityClaim artifact)
    evidenceAssumptions = qualificationEvidenceAssumptionRefs
      (steveProviderIdentityEvidence artifact)
    admissionConditions = Map.keysSet $ qualificationAdmissionConditionDispositions
      (steveProviderIdentityAdmission artifact)

digestSha256ConditionExplicitFact :: SteveProviderQualificationArtifact -> Bool
digestSha256ConditionExplicitFact artifact =
  conditions == Set.singleton sha256Condition
    && Set.member sha256Condition evidenceAssumptions
    && Set.member sha256Condition admissionConditions
  where
    sha256Condition = "assumption:sha256-semantic-profile.v1"
    conditions = qualificationClaimConditions (steveProviderIdentityClaim artifact)
    evidenceAssumptions = qualificationEvidenceAssumptionRefs
      (steveProviderIdentityEvidence artifact)
    admissionConditions = Map.keysSet $ qualificationAdmissionConditionDispositions
      (steveProviderIdentityAdmission artifact)

materializeDigestProvider
  :: Either SteveProviderQualificationError SteveProviderQualificationArtifact
materializeDigestProvider = do
  semantic <- liftCheck "DigestProvider semantic qualification" $
    checkProviderSemanticQualification
      digestProviderContract digestProviderImplementation digestProviderSemanticClaim
  computeCompetence <- liftCheck "DigestProvider compute competence" $
    checkProviderEvidenceProducerCompetence
      semantic digestComputeEvidenceRequirement digestComputeEvidenceClaim
  checkCompetence <- liftCheck "DigestProvider check competence" $
    checkProviderEvidenceProducerCompetence
      semantic digestCheckEvidenceRequirement digestCheckEvidenceClaim
  authority <- liftCheck "DigestProvider authority qualification" $
    checkProviderAuthorityQualification (Just semantic) digestAuthoritySpec
  let identityClaim = digestIdentityClaim
      identityEvidence = digestIdentityEvidence
      identityAdmission = mkAdmission
        "steve.digest-provider"
        digestProviderInterface
        identityClaim
        identityEvidence
        (qualificationClaimConditions identityClaim)
  checkedAdmission <- liftCheck "DigestProvider identity/admission" $
    checkQualificationAdmissionIdentity identityClaim identityEvidence identityAdmission
  pure SteveProviderQualificationArtifact
    { steveProviderLabel = "DigestProvider[SHA256]"
    , steveProviderContract = digestProviderContract
    , steveProviderImplementation = digestProviderImplementation
    , steveProviderSemanticClaim = digestProviderSemanticClaim
    , steveProviderCheckedSemantic = semantic
    , steveProviderStateRefinement = Nothing
    , steveProviderCheckedState = Nothing
    , steveProviderLaws = []
    , steveProviderLifecycleContract = Nothing
    , steveProviderLifecycleModel = Nothing
    , steveProviderCheckedLifecycle = Nothing
    , steveProviderEvidenceCompetences = [computeCompetence, checkCompetence]
    , steveProviderAuthoritySpec = digestAuthoritySpec
    , steveProviderCheckedAuthority = authority
    , steveProviderIdentityClaim = identityClaim
    , steveProviderIdentityEvidence = identityEvidence
    , steveProviderIdentityAdmission = identityAdmission
    , steveProviderCheckedAdmission = checkedAdmission
    , steveProviderRequiredObligationKeys = digestObligationKeys
    }

materializeBlobProvider
  :: Either SteveProviderQualificationError SteveProviderQualificationArtifact
materializeBlobProvider = do
  semantic <- liftCheck "BlobProvider semantic qualification" $
    checkProviderSemanticQualification
      blobProviderContract blobProviderImplementation blobProviderSemanticClaim
  checkedState <- liftCheck "BlobProvider state simulation" $
    checkProviderStateSimulation semantic blobStateRefinement
  checkedLaw <- liftCheck "BlobProvider no-replace law" $
    checkProviderLawCorpus semantic blobNoReplaceLaw blobLawEvidenceCorpus
  checkedLifecycle <- liftCheck "BlobProvider lifecycle qualification" $
    checkProviderLifecycleQualification
      semantic blobLifecycleContract blobLifecycleModel
  authority <- liftCheck "BlobProvider authority qualification" $
    checkProviderAuthorityQualification (Just semantic) blobAuthoritySpec
  let identityClaim = blobIdentityClaim
      identityEvidence = blobIdentityEvidence
      identityAdmission = mkAdmission
        "steve.blob-provider"
        blobProviderInterface
        identityClaim
        identityEvidence
        (qualificationClaimConditions identityClaim)
  checkedAdmission <- liftCheck "BlobProvider identity/admission" $
    checkQualificationAdmissionIdentity identityClaim identityEvidence identityAdmission
  pure SteveProviderQualificationArtifact
    { steveProviderLabel = "BlobProvider"
    , steveProviderContract = blobProviderContract
    , steveProviderImplementation = blobProviderImplementation
    , steveProviderSemanticClaim = blobProviderSemanticClaim
    , steveProviderCheckedSemantic = semantic
    , steveProviderStateRefinement = Just blobStateRefinement
    , steveProviderCheckedState = Just checkedState
    , steveProviderLaws = [(blobNoReplaceLaw, checkedLaw)]
    , steveProviderLifecycleContract = Just blobLifecycleContract
    , steveProviderLifecycleModel = Just blobLifecycleModel
    , steveProviderCheckedLifecycle = Just checkedLifecycle
    , steveProviderEvidenceCompetences = []
    , steveProviderAuthoritySpec = blobAuthoritySpec
    , steveProviderCheckedAuthority = authority
    , steveProviderIdentityClaim = identityClaim
    , steveProviderIdentityEvidence = identityEvidence
    , steveProviderIdentityAdmission = identityAdmission
    , steveProviderCheckedAdmission = checkedAdmission
    , steveProviderRequiredObligationKeys = blobObligationKeys
    }

liftCheck :: Show e => Text -> Either e a -> Either SteveProviderQualificationError a
liftCheck label = either
  (Left . SteveProviderQualificationError . ((label <> ": ") <>) . Text.pack . show)
  Right

-- Shared callable/resource helpers ------------------------------------------------

surface
  :: InterfaceRevision
  -> CallableMachineShape
  -> Set.Set SemanticEffect
  -> Set.Set CallableFailure
  -> CallableRefinementSurface
surface revision shape effects failures = CallableRefinementSurface
  { callableRefinementMachineShape = shape
  , callableRefinementContract = CallableContract revision PreserveCallee effects
  , callableRefinementCallerAuthority = Set.empty
  , callableRefinementFailures = failures
  }

emptyResidue :: ProviderResourceResidue
emptyResidue = ProviderResourceResidue
  { providerResidueBorrowedInputs = Set.empty
  , providerResidueConsumedInputs = Set.empty
  , providerResidueReturnedPredecessors = Set.empty
  , providerResidueSuccessors = Set.empty
  , providerResidueProducedResources = Set.empty
  }

mkAdmission
  :: Text
  -> InterfaceRevision
  -> ProviderQualificationClaimIdentityInput
  -> ProviderQualificationEvidenceIdentityInput
  -> Set.Set Text
  -> ProviderQualificationAdmissionIdentityInput
mkAdmission occurrence interface claim evidence conditions =
  ProviderQualificationAdmissionIdentityInput
    { qualificationAdmissionClaimRevision = deriveQualificationClaimRevision claim
    , qualificationAdmissionEvidenceRevision = deriveQualificationEvidenceRevision evidence
    , qualificationAdmissionProviderOccurrence = occurrence
    , qualificationAdmissionRequiredInterface = interface
    , qualificationAdmissionRealizationContextRevision =
        "steve.phase1.realization-context.v1"
    , qualificationAdmissionAssurancePolicyRevision =
        "phase1.steve-provider-pressure-policy.v1"
    , qualificationAdmissionConditionDispositions = Map.fromSet
        (const (SemanticAtom "accepted-for-phase1-pressure-case")) conditions
    , qualificationAdmissionDependencyAdmissions = Set.empty
    , qualificationAdmissionSelectedArtifactRuntimeAbi = Nothing
    , qualificationAdmissionExportedRuntimeObligations = Set.empty
    , qualificationAdmissionExportedDeploymentRequirements = Set.empty
    , qualificationAdmissionDecision = QualificationAdmitted
    }

-- DigestProvider -----------------------------------------------------------------

digestProviderInterface :: InterfaceRevision
digestProviderInterface = InterfaceRevision "steve.provider.digest.sha256.v1"

digestProviderDefinition :: DefinitionRevision
digestProviderDefinition = DefinitionRevision "steve.provider.digest.sha256.impl.v1"

digestComputeOperation, digestCheckOperation :: ProviderOperationKey
digestComputeOperation = ProviderOperationKey "digest.compute"
digestCheckOperation = ProviderOperationKey "digest.check"

digestComputeEntry, digestCheckEntry :: ProviderImplementationEntryKey
digestComputeEntry = ProviderImplementationEntryKey "steve.digest.impl.compute"
digestCheckEntry = ProviderImplementationEntryKey "steve.digest.impl.check"

digestComputeSuccess, digestCheckAccepted, digestCheckRejected :: ProviderOutcomeKey
digestComputeSuccess = ProviderOutcomeKey "digest.compute.success"
digestCheckAccepted = ProviderOutcomeKey "digest.check.accepted"
digestCheckRejected = ProviderOutcomeKey "digest.check.rejected"

digestImplComputeSuccess, digestImplCheckAccepted, digestImplCheckRejected :: ProviderOutcomeKey
digestImplComputeSuccess = ProviderOutcomeKey "impl.digest.compute.success"
digestImplCheckAccepted = ProviderOutcomeKey "impl.digest.check.accepted"
digestImplCheckRejected = ProviderOutcomeKey "impl.digest.check.rejected"

digestCandidateResource, digestIdResource, digestEvidenceResource :: ProviderResourceKey
digestCandidateResource = ProviderResourceKey "candidate-byte-view"
digestIdResource = ProviderResourceKey "content-id"
digestEvidenceResource = ProviderResourceKey "digest-evidence"

digestComputeResidue, digestCheckAcceptedResidue, digestCheckRejectedResidue :: ProviderResourceResidue
digestComputeResidue = emptyResidue
  { providerResidueBorrowedInputs = Set.singleton digestCandidateResource
  , providerResidueProducedResources = Set.fromList [digestIdResource, digestEvidenceResource]
  }
digestCheckAcceptedResidue = emptyResidue
  { providerResidueBorrowedInputs = Set.singleton digestCandidateResource
  , providerResidueProducedResources = Set.singleton digestEvidenceResource
  }
digestCheckRejectedResidue = emptyResidue
  { providerResidueBorrowedInputs = Set.singleton digestCandidateResource
  }

digestProviderContract :: ProviderContract
digestProviderContract = ProviderContract digestProviderInterface (Map.fromList
  [ (digestComputeOperation, ProviderOperationContract
      (surface
        (InterfaceRevision "steve.call.digest.compute.v1")
        (CallableMachineShape "borrowed-bytes->content-id+proof")
        (Set.singleton (SemanticEffect "digest.sha256.compute"))
        Set.empty)
      Set.empty
      (Map.singleton digestComputeSuccess digestComputeResidue))
  , (digestCheckOperation, ProviderOperationContract
      (surface
        (InterfaceRevision "steve.call.digest.check.v1")
        (CallableMachineShape "content-id+borrowed-bytes->digest-check")
        (Set.singleton (SemanticEffect "digest.sha256.check"))
        (Set.singleton (CallableTypedNegative (Outcome "digest-rejected"))))
      Set.empty
      (Map.fromList
        [ (digestCheckAccepted, digestCheckAcceptedResidue)
        , (digestCheckRejected, digestCheckRejectedResidue)
        ]))
  ])

digestProviderImplementation :: ProviderImplementation
digestProviderImplementation = ProviderImplementation
  digestProviderDefinition
  (Map.fromList
    [ (digestComputeEntry, ProviderImplementationOperation
        (surface
          (InterfaceRevision "steve.impl.digest.compute.v1")
          (CallableMachineShape "borrowed-bytes->content-id+proof")
          (Set.singleton (SemanticEffect "digest.sha256.compute"))
          Set.empty)
        Set.empty
        (Map.singleton digestImplComputeSuccess digestComputeResidue))
    , (digestCheckEntry, ProviderImplementationOperation
        (surface
          (InterfaceRevision "steve.impl.digest.check.v1")
          (CallableMachineShape "content-id+borrowed-bytes->digest-check")
          (Set.singleton (SemanticEffect "digest.sha256.check"))
          (Set.singleton (CallableTypedNegative (Outcome "digest-rejected"))))
        Set.empty
        (Map.fromList
          [ (digestImplCheckAccepted, digestCheckAcceptedResidue)
          , (digestImplCheckRejected, digestCheckRejectedResidue)
          ]))
    ])
  (Set.fromList ["sha256_compute", "sha256_check"])

digestProviderSemanticClaim :: ProviderQualificationClaim
digestProviderSemanticClaim = ProviderQualificationClaim
  digestProviderInterface
  digestProviderDefinition
  (Map.fromList
    [ (digestComputeOperation, ProviderOperationCorrespondence digestComputeEntry
        (Map.singleton digestImplComputeSuccess digestComputeSuccess))
    , (digestCheckOperation, ProviderOperationCorrespondence digestCheckEntry
        (Map.fromList
          [ (digestImplCheckAccepted, digestCheckAccepted)
          , (digestImplCheckRejected, digestCheckRejected)
          ]))
    ])

digestEvidenceFamily :: ProviderPropositionFamilyKey
digestEvidenceFamily = ProviderPropositionFamilyKey "DigestMatches"

digestComputeSubject, digestCheckSubject :: ProviderEvidenceSubjectKey
digestComputeSubject = ProviderEvidenceSubjectKey "role:steve-put-candidate-object"
digestCheckSubject = ProviderEvidenceSubjectKey "role:steve-get-read-object"

digestComputeIdParameter, digestCheckIdParameter :: RefTerm
digestComputeIdParameter = RefOpaque
  (SortStableId "content-id:sha256") "role:computed-content-id"
digestCheckIdParameter = RefOpaque
  (SortStableId "content-id:sha256") "role:requested-content-id"

digestComputeObservation, digestCheckObservation :: ProviderEvidenceObservation
digestComputeObservation = ScopedBorrowEvidenceObservation
  (ProviderObservationKey "role:steve-put-candidate-digest-view")
  (LoanScopeKey "steve.put.digest.borrow.v1")
digestCheckObservation = ScopedBorrowEvidenceObservation
  (ProviderObservationKey "role:steve-get-read-digest-view")
  (LoanScopeKey "steve.get.digest.borrow.v1")

digestEvidenceValidity :: EvidenceValidityContractKey
digestEvidenceValidity = EvidenceValidityContractKey
  "digest-matches-valid-while-stable-object-bytes-unchanged.v1"

digestComputeEvidenceRequirement, digestCheckEvidenceRequirement :: ProviderEvidenceProducerRequirement
digestComputeEvidenceRequirement = ProviderEvidenceProducerRequirement
  digestComputeOperation digestEvidenceFamily [digestComputeIdParameter]
  digestComputeSubject digestEvidenceValidity
digestCheckEvidenceRequirement = ProviderEvidenceProducerRequirement
  digestCheckOperation digestEvidenceFamily [digestCheckIdParameter]
  digestCheckSubject digestEvidenceValidity

digestComputeEvidenceClaim, digestCheckEvidenceClaim :: ProviderEvidenceProducerCompetenceClaim
digestComputeEvidenceClaim = ProviderEvidenceProducerCompetenceClaim
  digestComputeOperation digestEvidenceFamily [digestComputeIdParameter]
  digestComputeObservation digestComputeSubject
  (CheckedObservationToStableSubject
    (EvidenceSubjectMappingRevision "steve.digest.compute.borrow-to-owner.v1")
    digestComputeObservation digestComputeSubject)
  digestEvidenceValidity
digestCheckEvidenceClaim = ProviderEvidenceProducerCompetenceClaim
  digestCheckOperation digestEvidenceFamily [digestCheckIdParameter]
  digestCheckObservation digestCheckSubject
  (CheckedObservationToStableSubject
    (EvidenceSubjectMappingRevision "steve.digest.check.borrow-to-owner.v1")
    digestCheckObservation digestCheckSubject)
  digestEvidenceValidity

digestAuthoritySpec :: ProviderAuthorityQualificationSpec
digestAuthoritySpec = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = SemanticProviderAuthoritySubject
      digestProviderInterface digestProviderDefinition
  , providerAuthorityInventoryBasis = CheckedPurePhilAuthorityInventory
      (ProviderAuthorityInventoryRevision "steve.digest.authority-inventory.v1")
  , providerAuthorityClientVisible = Set.empty
  , providerAuthorityInternal = Set.empty
  , providerAuthorityPurePhilConfinements = []
  , providerAuthorityExtraDispositions = Map.empty
  }

digestObligationKeys :: Set.Set Text
digestObligationKeys = Set.fromList
  [ "operation.compute"
  , "operation.check"
  , "resource.borrow-preservation"
  , "evidence.compute.digest-matches"
  , "evidence.check.digest-matches"
  , "authority.no-storage-mutation"
  , "algorithm.sha256-profile"
  ]

digestIdentityClaim :: ProviderQualificationClaimIdentityInput
digestIdentityClaim = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = digestProviderInterface
  , qualificationClaimSubject = SemanticProviderImplementation digestProviderDefinition
  , qualificationClaimLayer = SemanticImplementationQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "checked:PROV-001-005")
      , ("borrow-preservation", SemanticAtom "candidate-view-borrowed-not-consumed:v1")
      , ("evidence", SemanticAtom "DigestMatches(id, stable-object):checked:PROV-010")
      , ("authority", SemanticAtom "no-storage-or-publication-authority:v1")
      ]
  , qualificationClaimConditions = Set.singleton "assumption:sha256-semantic-profile.v1"
  , qualificationClaimValidityScope = SemanticAtom "steve.digest-provider.validity.v1"
  }

digestIdentityEvidence :: ProviderQualificationEvidenceIdentityInput
digestIdentityEvidence = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision digestIdentityClaim
  , qualificationEvidenceObligationDispositions = Map.fromList
      [ ("operation.compute", SemanticAtom "discharged-by-callable-and-provider-refinement")
      , ("operation.check", SemanticAtom "discharged-by-callable-and-provider-refinement")
      , ("resource.borrow-preservation", SemanticAtom "discharged-by-exact-resource-residue")
      , ("evidence.compute.digest-matches", SemanticAtom "discharged-by-evidence-competence")
      , ("evidence.check.digest-matches", SemanticAtom "discharged-by-evidence-competence")
      , ("authority.no-storage-mutation", SemanticAtom "discharged-by-authority-inventory")
      , ("algorithm.sha256-profile", SemanticAtom "assumption-dependent")
      ]
  , qualificationEvidenceRefs = Set.fromList
      [ "steve.digest.compute.borrow-to-owner.v1"
      , "steve.digest.check.borrow-to-owner.v1"
      ]
  , qualificationEvidenceProofRefs = Set.empty
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs = Set.empty
  , qualificationEvidenceAssumptionRefs = Set.singleton "assumption:sha256-semantic-profile.v1"
  , qualificationEvidenceValidityDependencies = Set.singleton
      "digest-matches-valid-while-stable-object-bytes-unchanged.v1"
  }

-- BlobProvider -------------------------------------------------------------------

blobProviderInterface :: InterfaceRevision
blobProviderInterface = InterfaceRevision "steve.provider.blob.v1"

blobProviderDefinition :: DefinitionRevision
blobProviderDefinition = DefinitionRevision "steve.provider.blob.impl.v1"

blobReadOperation, blobInstallOperation :: ProviderOperationKey
blobReadOperation = ProviderOperationKey "blob.read"
blobInstallOperation = ProviderOperationKey "blob.install-if-absent"

blobReadEntry, blobInstallEntry :: ProviderImplementationEntryKey
blobReadEntry = ProviderImplementationEntryKey "steve.blob.impl.read"
blobInstallEntry = ProviderImplementationEntryKey "steve.blob.impl.install-if-absent"

blobReadFound, blobReadNotFound, blobReadStorageFailure :: ProviderOutcomeKey
blobReadFound = ProviderOutcomeKey "blob.read.found"
blobReadNotFound = ProviderOutcomeKey "blob.read.not-found"
blobReadStorageFailure = ProviderOutcomeKey "blob.read.storage-failure"

blobInstallInstalled, blobInstallAlreadyExists, blobInstallStorageFailure :: ProviderOutcomeKey
blobInstallInstalled = ProviderOutcomeKey "blob.install.installed"
blobInstallAlreadyExists = ProviderOutcomeKey "blob.install.already-exists"
blobInstallStorageFailure = ProviderOutcomeKey "blob.install.storage-failure"

blobImplReadFound, blobImplReadNotFound, blobImplReadStorageFailure :: ProviderOutcomeKey
blobImplReadFound = ProviderOutcomeKey "impl.blob.read.found"
blobImplReadNotFound = ProviderOutcomeKey "impl.blob.read.not-found"
blobImplReadStorageFailure = ProviderOutcomeKey "impl.blob.read.storage-failure"

blobImplInstallInstalled, blobImplInstallAlreadyExists, blobImplInstallStorageFailure :: ProviderOutcomeKey
blobImplInstallInstalled = ProviderOutcomeKey "impl.blob.install.installed"
blobImplInstallAlreadyExists = ProviderOutcomeKey "impl.blob.install.already-exists"
blobImplInstallStorageFailure = ProviderOutcomeKey "impl.blob.install.storage-failure"

blobCandidateResource, blobReadOwnerResource :: ProviderResourceKey
blobCandidateResource = ProviderResourceKey "steve-candidate-owner-borrow"
blobReadOwnerResource = ProviderResourceKey "blob-read-owned-bytes"

blobReadFoundResidue, blobReadEmptyResidue, blobInstallBorrowResidue :: ProviderResourceResidue
blobReadFoundResidue = emptyResidue
  { providerResidueProducedResources = Set.singleton blobReadOwnerResource }
blobReadEmptyResidue = emptyResidue
blobInstallBorrowResidue = emptyResidue
  { providerResidueBorrowedInputs = Set.singleton blobCandidateResource }

blobProviderContract :: ProviderContract
blobProviderContract = ProviderContract blobProviderInterface (Map.fromList
  [ (blobReadOperation, ProviderOperationContract
      (surface
        (InterfaceRevision "steve.call.blob.read.v1")
        (CallableMachineShape "content-id->owned-bytes-or-read-error")
        (Set.singleton (SemanticEffect "blob.read"))
        (Set.fromList
          [ CallableTypedNegative (Outcome "not-found")
          , CallableTypedNegative (Outcome "storage-failure")
          ]))
      Set.empty
      (Map.fromList
        [ (blobReadFound, blobReadFoundResidue)
        , (blobReadNotFound, blobReadEmptyResidue)
        , (blobReadStorageFailure, blobReadEmptyResidue)
        ]))
  , (blobInstallOperation, ProviderOperationContract
      (surface
        (InterfaceRevision "steve.call.blob.install.v1")
        (CallableMachineShape "content-id+borrowed-bytes->install-status")
        (Set.singleton (SemanticEffect "blob.install-if-absent"))
        (Set.fromList
          [ CallableTypedNegative (Outcome "already-exists")
          , CallableTypedNegative (Outcome "storage-failure")
          ]))
      Set.empty
      (Map.fromList
        [ (blobInstallInstalled, blobInstallBorrowResidue)
        , (blobInstallAlreadyExists, blobInstallBorrowResidue)
        , (blobInstallStorageFailure, blobInstallBorrowResidue)
        ]))
  ])

blobProviderImplementation :: ProviderImplementation
blobProviderImplementation = ProviderImplementation
  blobProviderDefinition
  (Map.fromList
    [ (blobReadEntry, ProviderImplementationOperation
        (surface
          (InterfaceRevision "steve.impl.blob.read.v1")
          (CallableMachineShape "content-id->owned-bytes-or-read-error")
          (Set.singleton (SemanticEffect "blob.read"))
          (Set.fromList
            [ CallableTypedNegative (Outcome "not-found")
            , CallableTypedNegative (Outcome "storage-failure")
            ]))
        Set.empty
        (Map.fromList
          [ (blobImplReadFound, blobReadFoundResidue)
          , (blobImplReadNotFound, blobReadEmptyResidue)
          , (blobImplReadStorageFailure, blobReadEmptyResidue)
          ]))
    , (blobInstallEntry, ProviderImplementationOperation
        (surface
          (InterfaceRevision "steve.impl.blob.install.v1")
          (CallableMachineShape "content-id+borrowed-bytes->install-status")
          (Set.singleton (SemanticEffect "blob.install-if-absent"))
          (Set.fromList
            [ CallableTypedNegative (Outcome "already-exists")
            , CallableTypedNegative (Outcome "storage-failure")
            ]))
        Set.empty
        (Map.fromList
          [ (blobImplInstallInstalled, blobInstallBorrowResidue)
          , (blobImplInstallAlreadyExists, blobInstallBorrowResidue)
          , (blobImplInstallStorageFailure, blobInstallBorrowResidue)
          ]))
    ])
  (Set.fromList ["blob_read", "blob_install_if_absent"])

blobProviderSemanticClaim :: ProviderQualificationClaim
blobProviderSemanticClaim = ProviderQualificationClaim
  blobProviderInterface
  blobProviderDefinition
  (Map.fromList
    [ (blobReadOperation, ProviderOperationCorrespondence blobReadEntry
        (Map.fromList
          [ (blobImplReadFound, blobReadFound)
          , (blobImplReadNotFound, blobReadNotFound)
          , (blobImplReadStorageFailure, blobReadStorageFailure)
          ]))
    , (blobInstallOperation, ProviderOperationCorrespondence blobInstallEntry
        (Map.fromList
          [ (blobImplInstallInstalled, blobInstallInstalled)
          , (blobImplInstallAlreadyExists, blobInstallAlreadyExists)
          , (blobImplInstallStorageFailure, blobInstallStorageFailure)
          ]))
    ])

blobImplEmptyState, blobImplFullState :: ProviderImplementationStateKey
blobImplEmptyState = ProviderImplementationStateKey "impl.empty"
blobImplFullState = ProviderImplementationStateKey "impl.object-present"

blobAbstractEmptyState, blobAbstractFullState :: ProviderAbstractStateKey
blobAbstractEmptyState = ProviderAbstractStateKey "abstract.absent"
blobAbstractFullState = ProviderAbstractStateKey "abstract.present-complete"

blobStateRefinement :: ProviderStateRefinement
blobStateRefinement = ProviderStateRefinement
  { providerStateRelationRevision = ProviderStateRelationRevision
      "steve.blob.append-only-state-relation.v1"
  , providerStateRelatedPairs = Set.fromList
      [ ProviderStatePair blobImplEmptyState blobAbstractEmptyState
      , ProviderStatePair blobImplFullState blobAbstractFullState
      ]
  , providerStateVisibleInitialImplementationStates = Set.singleton blobImplEmptyState
  , providerStateAdmissibleInitialAbstractStates = Set.singleton blobAbstractEmptyState
  , providerStateInitialCorrespondence = Map.singleton blobImplEmptyState blobAbstractEmptyState
  , providerStateImplementationTransitions = Set.fromList
      [ implTransition blobInstallOperation blobImplEmptyState blobImplInstallInstalled blobImplFullState
      , implTransition blobInstallOperation blobImplFullState blobImplInstallAlreadyExists blobImplFullState
      , implTransition blobInstallOperation blobImplEmptyState blobImplInstallStorageFailure blobImplEmptyState
      , implTransition blobInstallOperation blobImplFullState blobImplInstallStorageFailure blobImplFullState
      , implTransition blobReadOperation blobImplEmptyState blobImplReadNotFound blobImplEmptyState
      , implTransition blobReadOperation blobImplFullState blobImplReadFound blobImplFullState
      , implTransition blobReadOperation blobImplEmptyState blobImplReadStorageFailure blobImplEmptyState
      , implTransition blobReadOperation blobImplFullState blobImplReadStorageFailure blobImplFullState
      ]
  , providerStateContractTransitions = Set.fromList
      [ contractTransition blobInstallOperation blobAbstractEmptyState blobInstallInstalled blobAbstractFullState
      , contractTransition blobInstallOperation blobAbstractFullState blobInstallAlreadyExists blobAbstractFullState
      , contractTransition blobInstallOperation blobAbstractEmptyState blobInstallStorageFailure blobAbstractEmptyState
      , contractTransition blobInstallOperation blobAbstractFullState blobInstallStorageFailure blobAbstractFullState
      , contractTransition blobReadOperation blobAbstractEmptyState blobReadNotFound blobAbstractEmptyState
      , contractTransition blobReadOperation blobAbstractFullState blobReadFound blobAbstractFullState
      , contractTransition blobReadOperation blobAbstractEmptyState blobReadStorageFailure blobAbstractEmptyState
      , contractTransition blobReadOperation blobAbstractFullState blobReadStorageFailure blobAbstractFullState
      ]
  }
  where
    implTransition = ProviderImplementationStateTransition
    contractTransition = ProviderContractStateTransition

blobLawEmpty, blobLawFull :: ProviderLawStateKey
blobLawEmpty = ProviderLawStateKey "law.absent"
blobLawFull = ProviderLawStateKey "law.present"

publicEvent :: ProviderOperationKey -> ProviderOutcomeKey -> ProviderPublicEvent
publicEvent = ProviderPublicEvent

blobNoReplaceLaw :: ProviderLaw
blobNoReplaceLaw = ProviderLaw
  { providerLawRevision = ProviderLawRevision "steve.blob.no-replace-law.v1"
  , providerLawInitialState = blobLawEmpty
  , providerLawTransitions = Map.fromList
      [ ((blobLawEmpty, publicEvent blobInstallOperation blobInstallInstalled), blobLawFull)
      , ((blobLawEmpty, publicEvent blobInstallOperation blobInstallStorageFailure), blobLawEmpty)
      , ((blobLawEmpty, publicEvent blobReadOperation blobReadNotFound), blobLawEmpty)
      , ((blobLawEmpty, publicEvent blobReadOperation blobReadStorageFailure), blobLawEmpty)
      , ((blobLawFull, publicEvent blobInstallOperation blobInstallAlreadyExists), blobLawFull)
      , ((blobLawFull, publicEvent blobInstallOperation blobInstallStorageFailure), blobLawFull)
      , ((blobLawFull, publicEvent blobReadOperation blobReadFound), blobLawFull)
      , ((blobLawFull, publicEvent blobReadOperation blobReadStorageFailure), blobLawFull)
      ]
  }

blobLawEvidenceCorpus :: Map.Map ProviderImplementationTraceKey [ProviderImplementationEvent]
blobLawEvidenceCorpus = Map.fromList
  [ (ProviderImplementationTraceKey "install-then-read",
      [ ProviderImplementationEvent blobInstallOperation blobImplInstallInstalled
      , ProviderImplementationEvent blobReadOperation blobImplReadFound
      ])
  , (ProviderImplementationTraceKey "empty-read",
      [ProviderImplementationEvent blobReadOperation blobImplReadNotFound])
  , (ProviderImplementationTraceKey "repeat-install",
      [ ProviderImplementationEvent blobInstallOperation blobImplInstallInstalled
      , ProviderImplementationEvent blobInstallOperation blobImplInstallAlreadyExists
      ])
  ]

blobObservationBoundary :: ProviderObservationBoundaryKey
blobObservationBoundary = ProviderObservationBoundaryKey "steve.blob.client-visible-namespace.v1"

blobBeforePublicationPoint, blobAfterPublicationPoint :: ProviderLifecyclePoint
blobBeforePublicationPoint = ProviderLifecyclePoint blobInstallOperation
  (ProviderInterruptionPointKey "install.before-publication")
blobAfterPublicationPoint = ProviderLifecyclePoint blobInstallOperation
  (ProviderInterruptionPointKey "install.after-publication-before-return")

blobAbsentObservable, blobCompleteObservable :: ProviderObservableStateKey
blobAbsentObservable = ProviderObservableStateKey "object.absent"
blobCompleteObservable = ProviderObservableStateKey "object.complete-and-correct"

blobLifecycleAllowanceBefore, blobLifecycleAllowanceAfter :: ProviderLifecycleAllowance
blobLifecycleAllowanceBefore = ProviderLifecycleAllowance
  (Set.singleton blobAbsentObservable)
  (Set.singleton emptyResidue)
  (Set.singleton ProviderRetrySameOperation)
blobLifecycleAllowanceAfter = ProviderLifecycleAllowance
  (Set.singleton blobCompleteObservable)
  (Set.singleton emptyResidue)
  (Set.singleton ProviderRetrySameOperation)

blobLifecycleContract :: ProviderLifecycleContract
blobLifecycleContract = ProviderLifecycleContract
  { providerLifecycleRevision = ProviderLifecycleRevision
      "steve.blob.atomic-publication-lifecycle.v1"
  , providerLifecycleObservationBoundary = blobObservationBoundary
  , providerLifecycleAllowances = Map.fromList
      [ (blobBeforePublicationPoint, blobLifecycleAllowanceBefore)
      , (blobAfterPublicationPoint, blobLifecycleAllowanceAfter)
      ]
  }

blobLifecycleModel :: ProviderLifecycleModel
blobLifecycleModel = ProviderLifecycleModel (Map.fromList
  [ (blobBeforePublicationPoint, Set.singleton ProviderInterruptionObservation
      { providerInterruptionObservationBoundary = blobObservationBoundary
      , providerInterruptionObservableState = blobAbsentObservable
      , providerInterruptionCleanupResidue = emptyResidue
      , providerInterruptionRetryDisposition = ProviderRetrySameOperation
      })
  , (blobAfterPublicationPoint, Set.singleton ProviderInterruptionObservation
      { providerInterruptionObservationBoundary = blobObservationBoundary
      , providerInterruptionObservableState = blobCompleteObservable
      , providerInterruptionCleanupResidue = emptyResidue
      , providerInterruptionRetryDisposition = ProviderRetrySameOperation
      })
  ])

blobAuthoritySubjectKey :: AuthoritySubjectKey
blobAuthoritySubjectKey = AuthoritySubjectKey "steve.blob.namespace"

blobAuthorityRead, blobAuthorityInstall, blobAuthorityOverwrite, blobAuthorityDelete :: AuthorityUse
blobAuthorityRead = AuthorityUse blobAuthoritySubjectKey (AuthorityOperationKey "read")
blobAuthorityInstall = AuthorityUse blobAuthoritySubjectKey (AuthorityOperationKey "install-if-absent")
blobAuthorityOverwrite = AuthorityUse blobAuthoritySubjectKey (AuthorityOperationKey "overwrite")
blobAuthorityDelete = AuthorityUse blobAuthoritySubjectKey (AuthorityOperationKey "delete")

blobConfinementAssumption :: ProviderAuthorityAssumptionKey
blobConfinementAssumption = ProviderAuthorityAssumptionKey
  "assumption:steve.blob.backing-authority-confined.v1"

blobAuthoritySpec :: ProviderAuthorityQualificationSpec
blobAuthoritySpec = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = SemanticProviderAuthoritySubject
      blobProviderInterface blobProviderDefinition
  , providerAuthorityInventoryBasis = CheckedPurePhilAuthorityInventory
      (ProviderAuthorityInventoryRevision "steve.blob.authority-inventory.v1")
  , providerAuthorityClientVisible = Set.fromList
      [blobAuthorityRead, blobAuthorityInstall]
  , providerAuthorityInternal = Set.fromList
      [ blobAuthorityRead
      , blobAuthorityInstall
      , blobAuthorityOverwrite
      , blobAuthorityDelete
      ]
  , providerAuthorityPurePhilConfinements = []
  , providerAuthorityExtraDispositions = Map.fromList
      [ (blobAuthorityOverwrite, ExtraAuthorityAssumptionDependent blobConfinementAssumption)
      , (blobAuthorityDelete, ExtraAuthorityAssumptionDependent blobConfinementAssumption)
      ]
  }

blobConditions :: Set.Set Text
blobConditions = Set.fromList
  [ "assumption:steve.blob.backing-authority-confined.v1"
  , "assumption:steve.blob.no-out-of-band-mutation.v1"
  , "assumption:steve.blob.atomic-no-replace-publication.v1"
  , "assumption:steve.blob.complete-copy-before-candidate-borrow-end.v1"
  ]

blobObligationKeys :: Set.Set Text
blobObligationKeys = Set.fromList
  [ "operation.read"
  , "operation.install-if-absent"
  , "resource.candidate-borrow-preserved"
  , "state.append-only-simulation"
  , "law.no-replace"
  , "lifecycle.atomic-publication"
  , "lifecycle.cleanup-and-retry"
  , "authority.narrow-client-surface"
  , "interference.no-out-of-band-mutation"
  , "borrow.complete-before-scope-end"
  ]

blobIdentityClaim :: ProviderQualificationClaimIdentityInput
blobIdentityClaim = ProviderQualificationClaimIdentityInput
  { qualificationClaimRequiredInterface = blobProviderInterface
  , qualificationClaimSubject = SemanticProviderImplementation blobProviderDefinition
  , qualificationClaimLayer = SemanticImplementationQualification
  , qualificationClaimSemanticRelations = Map.fromList
      [ ("operations", SemanticAtom "checked:PROV-001-005")
      , ("candidate-borrow", SemanticAtom "borrowed-not-consumed-on-all-install-outcomes:v1")
      , ("state", SemanticAtom "steve.blob.append-only-state-relation.v1")
      , ("law", SemanticAtom "steve.blob.no-replace-law.v1")
      , ("lifecycle", SemanticAtom "steve.blob.atomic-publication-lifecycle.v1")
      , ("authority", SemanticAtom "narrow-read-install-over-broad-backing-authority:v1")
      ]
  , qualificationClaimConditions = blobConditions
  , qualificationClaimValidityScope = SemanticAtom "steve.blob-provider.validity.v1"
  }

blobIdentityEvidence :: ProviderQualificationEvidenceIdentityInput
blobIdentityEvidence = ProviderQualificationEvidenceIdentityInput
  { qualificationEvidenceClaimRevision = deriveQualificationClaimRevision blobIdentityClaim
  , qualificationEvidenceObligationDispositions = Map.fromList
      [ ("operation.read", SemanticAtom "discharged-by-callable-and-provider-refinement")
      , ("operation.install-if-absent", SemanticAtom "discharged-by-callable-and-provider-refinement")
      , ("resource.candidate-borrow-preserved", SemanticAtom "discharged-by-exact-resource-residue")
      , ("state.append-only-simulation", SemanticAtom "discharged-by-state-simulation")
      , ("law.no-replace", SemanticAtom "conditioned-on-law-coverage-evidence")
      , ("lifecycle.atomic-publication", SemanticAtom "conditioned-on-interruption-model-evidence")
      , ("lifecycle.cleanup-and-retry", SemanticAtom "discharged-by-lifecycle-relation")
      , ("authority.narrow-client-surface", SemanticAtom "assumption-dependent-confinement")
      , ("interference.no-out-of-band-mutation", SemanticAtom "assumption-dependent")
      , ("borrow.complete-before-scope-end", SemanticAtom "assumption-plus-lifecycle-boundary")
      ]
  , qualificationEvidenceRefs = Set.fromList
      [ "steve.blob.append-only-state-relation.v1"
      , "steve.blob.no-replace-law.v1"
      , "steve.blob.atomic-publication-lifecycle.v1"
      ]
  , qualificationEvidenceProofRefs = Set.empty
  , qualificationEvidenceTranslationValidationRefs = Set.empty
  , qualificationEvidenceRuntimeEnforcementRefs = Set.empty
  , qualificationEvidenceAssumptionRefs = blobConditions
  , qualificationEvidenceValidityDependencies = Set.fromList
      [ "steve.blob.client-visible-namespace.v1"
      , "steve.blob-provider.validity.v1"
      ]
  }
