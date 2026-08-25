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

  requireAdmittedPrior priorAdmission
  requireAdmittedNew newAdmission

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

  requireEqual ProviderReplacementInterfaceMismatch requiredInterface newInterface
  requireEqual ProviderReplacementOccurrenceMismatch priorOccurrence newOccurrence
  requireEqual ProviderReplacementInstanceMismatch
    (providerReplacementInstanceRevision prior)
    (providerReplacementInstanceRevision replacement)

  if priorSubject == newSubject
    then Left (ProviderReplacementSameImplementationSubject priorSubject)
    else Right ()
  if providerReplacementRealizationRevision prior ==
      providerReplacementRealizationRevision replacement
    then Left (ProviderReplacementRealizationUnchanged
      (providerReplacementRealizationRevision prior))
    else Right ()
  if priorClaimRevision == newClaimRevision
    then Left (ProviderReplacementClaimLineageInherited priorClaimRevision)
    else Right ()
  if priorEvidenceRevision == newEvidenceRevision
    then Left (ProviderReplacementEvidenceLineageInherited priorEvidenceRevision)
    else Right ()
  if priorAdmissionRevision == newAdmissionRevision
    then Left (ProviderReplacementAdmissionLineageInherited priorAdmissionRevision)
    else Right ()

  if not (Set.null missingReuse)
    then Left (ProviderReplacementSharedEvidenceWithoutScope missingReuse)
    else Right ()
  if not (Set.null unexpectedReuse)
    then Left (ProviderReplacementUnexpectedReuseJustification unexpectedReuse)
    else Right ()

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
    validateReuse priorClaimRevision newClaimRevision (key, reuse) = do
      requireEqual ProviderReplacementReuseReferenceMismatch
        key (providerReplacementReuseReference reuse)
      requireEqual ProviderReplacementReusePriorClaimMismatch
        priorClaimRevision (providerReplacementReusePriorClaimRevision reuse)
      requireEqual ProviderReplacementReuseNewClaimMismatch
        newClaimRevision (providerReplacementReuseNewClaimRevision reuse)
      if Text.null (providerReplacementReuseValidityScopeRevision reuse)
        then Left (ProviderReplacementReuseScopeMissing key)
        else Right ()

requireAdmittedPrior
  :: CheckedProviderQualificationAdmissionIdentity
  -> Either ProviderReplacementQualificationError ()
requireAdmittedPrior checked = case checkedQualificationAdmissionDecision checked of
  QualificationAdmitted -> Right ()
  QualificationRejected reasons ->
    Left (ProviderReplacementPriorAdmissionRejected reasons)

requireAdmittedNew
  :: CheckedProviderQualificationAdmissionIdentity
  -> Either ProviderReplacementQualificationError ()
requireAdmittedNew checked = case checkedQualificationAdmissionDecision checked of
  QualificationAdmitted -> Right ()
  QualificationRejected reasons ->
    Left (ProviderReplacementNewAdmissionRejected reasons)

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

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
