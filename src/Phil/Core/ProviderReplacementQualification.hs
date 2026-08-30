{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderReplacementQualification
  ( ProviderReplacementSide (..)
  , ProviderReplacementEvidenceReferenceKind (..)
  , ProviderReplacementEvidenceReference (..)
  , ProviderReplacementEvidenceReuse (..)
  , CheckedProviderReplacementQualification (..)
  , ProviderReplacementQualificationError (..)
  , checkProviderReplacementQualification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified ProviderReplacementQualificationKernel as Kernel
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationAdmissionDecision (..)
  , ProviderQualificationAdmissionIdentityInput (..)
  , ProviderQualificationClaimIdentityInput (..)
  , ProviderQualificationEvidenceIdentityInput (..)
  , ProviderQualificationIdentityError
  , ProviderQualificationSubject
  , QualificationAdmissionRevision
  , QualificationClaimRevision
  , QualificationEvidenceRevision
  , checkQualificationAdmissionIdentity
  )
import Phil.Core.Static
  ( InstanceRevision
  , InterfaceRevision
  , RealizationRevision
  )

-- | One independently checkable side of a build-time provider replacement.
-- Both predecessor and replacement are rechecked from raw claim/evidence/
-- admission inputs; the replacement never inherits a checked predecessor object.
data ProviderReplacementSide = ProviderReplacementSide
  { providerReplacementClaim :: ProviderQualificationClaimIdentityInput
  , providerReplacementEvidence :: ProviderQualificationEvidenceIdentityInput
  , providerReplacementAdmission :: ProviderQualificationAdmissionIdentityInput
  , providerReplacementInstanceRevision :: InstanceRevision
  , providerReplacementRealizationRevision :: RealizationRevision
  }
  deriving (Eq, Ord, Show)

data ProviderReplacementEvidenceReferenceKind
  = GeneralEvidenceReference
  | ProofOrCertificateReference
  | TranslationValidationReference
  | RuntimeEnforcementReference
  | AssumptionReference
  | ValidityDependencyReference
  deriving (Eq, Ord, Show)

data ProviderReplacementEvidenceReference = ProviderReplacementEvidenceReference
  { providerReplacementEvidenceReferenceKind :: ProviderReplacementEvidenceReferenceKind
  , providerReplacementEvidenceReferenceValue :: Text
  }
  deriving (Eq, Ord, Show)

-- | Explicit justification for deliberately reusing one evidence reference on
-- both qualification claims. Reuse is legal only when its own validity scope is
-- asserted to apply independently to both exact claim revisions.
data ProviderReplacementEvidenceReuse = ProviderReplacementEvidenceReuse
  { providerReplacementReuseReference :: ProviderReplacementEvidenceReference
  , providerReplacementReusePriorClaimRevision :: QualificationClaimRevision
  , providerReplacementReuseNewClaimRevision :: QualificationClaimRevision
  , providerReplacementReuseValidityScopeRevision :: Text
  }
  deriving (Eq, Ord, Show)

data CheckedProviderReplacementQualification = CheckedProviderReplacementQualification
  { checkedProviderReplacementRequiredInterface :: InterfaceRevision
  , checkedProviderReplacementOccurrence :: Text
  , checkedProviderReplacementInstanceRevision :: InstanceRevision
  , checkedProviderReplacementPriorSubject :: ProviderQualificationSubject
  , checkedProviderReplacementNewSubject :: ProviderQualificationSubject
  , checkedProviderReplacementPriorClaimRevision :: QualificationClaimRevision
  , checkedProviderReplacementNewClaimRevision :: QualificationClaimRevision
  , checkedProviderReplacementPriorEvidenceRevision :: QualificationEvidenceRevision
  , checkedProviderReplacementNewEvidenceRevision :: QualificationEvidenceRevision
  , checkedProviderReplacementPriorAdmissionRevision :: QualificationAdmissionRevision
  , checkedProviderReplacementNewAdmissionRevision :: QualificationAdmissionRevision
  , checkedProviderReplacementPriorRealizationRevision :: RealizationRevision
  , checkedProviderReplacementNewRealizationRevision :: RealizationRevision
  , checkedProviderReplacementReusedEvidence
      :: Set.Set ProviderReplacementEvidenceReference
  }
  deriving (Eq, Ord, Show)

data ProviderReplacementQualificationError
  = ProviderReplacementPriorIdentityError ProviderQualificationIdentityError
  | ProviderReplacementNewIdentityError ProviderQualificationIdentityError
  | ProviderReplacementPriorAdmissionRejected (Set.Set Text)
  | ProviderReplacementNewAdmissionRejected (Set.Set Text)
  | ProviderReplacementInterfaceMismatch InterfaceRevision InterfaceRevision
  | ProviderReplacementOccurrenceMismatch Text Text
  | ProviderReplacementInstanceMismatch InstanceRevision InstanceRevision
  | ProviderReplacementSameImplementationSubject ProviderQualificationSubject
  | ProviderReplacementRealizationUnchanged RealizationRevision
  | ProviderReplacementClaimLineageInherited QualificationClaimRevision
  | ProviderReplacementEvidenceLineageInherited QualificationEvidenceRevision
  | ProviderReplacementAdmissionLineageInherited QualificationAdmissionRevision
  | ProviderReplacementSharedEvidenceWithoutScope
      (Set.Set ProviderReplacementEvidenceReference)
  | ProviderReplacementUnexpectedReuseJustification
      (Set.Set ProviderReplacementEvidenceReference)
  | ProviderReplacementReuseReferenceMismatch
      ProviderReplacementEvidenceReference ProviderReplacementEvidenceReference
  | ProviderReplacementReusePriorClaimMismatch
      QualificationClaimRevision QualificationClaimRevision
  | ProviderReplacementReuseNewClaimMismatch
      QualificationClaimRevision QualificationClaimRevision
  | ProviderReplacementReuseScopeMissing ProviderReplacementEvidenceReference
  deriving (Eq, Ord, Show)

checkProviderReplacementQualification
  :: ProviderReplacementSide
  -> ProviderReplacementSide
  -> Map.Map ProviderReplacementEvidenceReference ProviderReplacementEvidenceReuse
  -> Either ProviderReplacementQualificationError CheckedProviderReplacementQualification
checkProviderReplacementQualification prior replacement reusePlan = do
  priorAdmission <- mapLeft ProviderReplacementPriorIdentityError $
    checkQualificationAdmissionIdentity
      (providerReplacementClaim prior)
      (providerReplacementEvidence prior)
      (providerReplacementAdmission prior)
  newAdmission <- mapLeft ProviderReplacementNewIdentityError $
    checkQualificationAdmissionIdentity
      (providerReplacementClaim replacement)
      (providerReplacementEvidence replacement)
      (providerReplacementAdmission replacement)

  let priorClaimInput = providerReplacementClaim prior
      newClaimInput = providerReplacementClaim replacement
      priorAdmissionInput = providerReplacementAdmission prior
      newAdmissionInput = providerReplacementAdmission replacement
      requiredInterface = qualificationClaimRequiredInterface priorClaimInput
      newInterface = qualificationClaimRequiredInterface newClaimInput
      priorOccurrence = qualificationAdmissionProviderOccurrence priorAdmissionInput
      newOccurrence = qualificationAdmissionProviderOccurrence newAdmissionInput
      priorSubject = qualificationClaimSubject priorClaimInput
      newSubject = qualificationClaimSubject newClaimInput
      priorClaimRevision = checkedQualificationAdmissionClaimRevision priorAdmission
      newClaimRevision = checkedQualificationAdmissionClaimRevision newAdmission
      priorEvidenceRevision = checkedQualificationAdmissionEvidenceRevision priorAdmission
      newEvidenceRevision = checkedQualificationAdmissionEvidenceRevision newAdmission
      priorAdmissionRevision = checkedQualificationAdmissionRevision priorAdmission
      newAdmissionRevision = checkedQualificationAdmissionRevision newAdmission
      priorRefs = evidenceReferences (providerReplacementEvidence prior)
      newRefs = evidenceReferences (providerReplacementEvidence replacement)
      sharedRefs = Set.intersection priorRefs newRefs
      reuseKeys = Map.keysSet reusePlan
      missingReuse = Set.difference sharedRefs reuseKeys
      unexpectedReuse = Set.difference reuseKeys sharedRefs

  case Kernel.decideProviderReplacementByFacts
    (providerReplacementAdmissionAccepted priorAdmission)
    (providerReplacementAdmissionAccepted newAdmission)
    (requiredInterface == newInterface)
    (priorOccurrence == newOccurrence)
    (providerReplacementInstanceRevision prior ==
      providerReplacementInstanceRevision replacement)
    (priorSubject /= newSubject)
    (providerReplacementRealizationRevision prior /=
      providerReplacementRealizationRevision replacement)
    (priorClaimRevision /= newClaimRevision)
    (priorEvidenceRevision /= newEvidenceRevision)
    (priorAdmissionRevision /= newAdmissionRevision)
    (Set.null missingReuse)
    (Set.null unexpectedReuse) of
    Kernel.ProviderReplacementAccepted -> Right ()
    Kernel.ProviderReplacementAdmissionRequired ->
      case checkedQualificationAdmissionDecision priorAdmission of
        QualificationRejected reasons ->
          Left (ProviderReplacementPriorAdmissionRejected reasons)
        QualificationAdmitted ->
          case checkedQualificationAdmissionDecision newAdmission of
            QualificationRejected reasons ->
              Left (ProviderReplacementNewAdmissionRejected reasons)
            QualificationAdmitted ->
              providerReplacementKernelBridgeMismatch "admission"
    Kernel.ProviderReplacementInterfaceMismatch ->
      Left (ProviderReplacementInterfaceMismatch requiredInterface newInterface)
    Kernel.ProviderReplacementOccurrenceMismatch ->
      Left (ProviderReplacementOccurrenceMismatch priorOccurrence newOccurrence)
    Kernel.ProviderReplacementInstanceMismatch ->
      Left (ProviderReplacementInstanceMismatch
        (providerReplacementInstanceRevision prior)
        (providerReplacementInstanceRevision replacement))
    Kernel.ProviderReplacementSameSemanticSubject ->
      Left (ProviderReplacementSameImplementationSubject priorSubject)
    Kernel.ProviderReplacementRealizationUnchanged ->
      Left (ProviderReplacementRealizationUnchanged
        (providerReplacementRealizationRevision prior))
    Kernel.ProviderReplacementClaimLineageInherited ->
      Left (ProviderReplacementClaimLineageInherited priorClaimRevision)
    Kernel.ProviderReplacementEvidenceLineageInherited ->
      Left (ProviderReplacementEvidenceLineageInherited priorEvidenceRevision)
    Kernel.ProviderReplacementAdmissionLineageInherited ->
      Left (ProviderReplacementAdmissionLineageInherited priorAdmissionRevision)
    Kernel.ProviderReplacementSharedEvidenceWithoutScope ->
      Left (ProviderReplacementSharedEvidenceWithoutScope missingReuse)
    Kernel.ProviderReplacementUnexpectedEvidenceReuse ->
      Left (ProviderReplacementUnexpectedReuseJustification unexpectedReuse)

  mapM_ (validateReuse priorClaimRevision newClaimRevision)
    (Map.toAscList reusePlan)

  Right CheckedProviderReplacementQualification
    { checkedProviderReplacementRequiredInterface = requiredInterface
    , checkedProviderReplacementOccurrence = priorOccurrence
    , checkedProviderReplacementInstanceRevision =
        providerReplacementInstanceRevision prior
    , checkedProviderReplacementPriorSubject = priorSubject
    , checkedProviderReplacementNewSubject = newSubject
    , checkedProviderReplacementPriorClaimRevision = priorClaimRevision
    , checkedProviderReplacementNewClaimRevision = newClaimRevision
    , checkedProviderReplacementPriorEvidenceRevision = priorEvidenceRevision
    , checkedProviderReplacementNewEvidenceRevision = newEvidenceRevision
    , checkedProviderReplacementPriorAdmissionRevision = priorAdmissionRevision
    , checkedProviderReplacementNewAdmissionRevision = newAdmissionRevision
    , checkedProviderReplacementPriorRealizationRevision =
        providerReplacementRealizationRevision prior
    , checkedProviderReplacementNewRealizationRevision =
        providerReplacementRealizationRevision replacement
    , checkedProviderReplacementReusedEvidence = sharedRefs
    }
  where
    validateReuse priorClaimRevision newClaimRevision (key, reuse) =
      case Kernel.decideProviderReplacementReuseByFacts
          (key == providerReplacementReuseReference reuse)
          (priorClaimRevision == providerReplacementReusePriorClaimRevision reuse)
          (newClaimRevision == providerReplacementReuseNewClaimRevision reuse)
          (not (Text.null (providerReplacementReuseValidityScopeRevision reuse))) of
        Kernel.ProviderReplacementReuseAccepted -> Right ()
        Kernel.ProviderReplacementReuseReferenceMismatch ->
          Left (ProviderReplacementReuseReferenceMismatch
            key (providerReplacementReuseReference reuse))
        Kernel.ProviderReplacementReusePriorClaimMismatch ->
          Left (ProviderReplacementReusePriorClaimMismatch
            priorClaimRevision (providerReplacementReusePriorClaimRevision reuse))
        Kernel.ProviderReplacementReuseNewClaimMismatch ->
          Left (ProviderReplacementReuseNewClaimMismatch
            newClaimRevision (providerReplacementReuseNewClaimRevision reuse))
        Kernel.ProviderReplacementReuseScopeMissing ->
          Left (ProviderReplacementReuseScopeMissing key)

providerReplacementAdmissionAccepted
  :: CheckedProviderQualificationAdmissionIdentity
  -> Bool
providerReplacementAdmissionAccepted checked =
  case checkedQualificationAdmissionDecision checked of
    QualificationAdmitted -> True
    QualificationRejected _ -> False

providerReplacementKernelBridgeMismatch :: String -> a
providerReplacementKernelBridgeMismatch seam =
  error ("ProviderReplacementQualificationKernel bridge mismatch: " <> seam)

evidenceReferences
  :: ProviderQualificationEvidenceIdentityInput
  -> Set.Set ProviderReplacementEvidenceReference
evidenceReferences evidence = Set.unions
  [ tagged GeneralEvidenceReference (qualificationEvidenceRefs evidence)
  , tagged ProofOrCertificateReference (qualificationEvidenceProofRefs evidence)
  , tagged TranslationValidationReference
      (qualificationEvidenceTranslationValidationRefs evidence)
  , tagged RuntimeEnforcementReference
      (qualificationEvidenceRuntimeEnforcementRefs evidence)
  , tagged AssumptionReference (qualificationEvidenceAssumptionRefs evidence)
  , tagged ValidityDependencyReference
      (qualificationEvidenceValidityDependencies evidence)
  ]
  where
    tagged kind = Set.map (ProviderReplacementEvidenceReference kind)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
