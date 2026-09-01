{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderQualificationApplicability
  ( ProviderRequirementOccurrenceKey (..)
  , ProviderConcreteAdmissionApplicability (..)
  , SelectedProviderRealization (..)
  , CheckedProviderAdmissionApplicability (..)
  , ProviderAdmissionApplicabilityError (..)
  , checkProviderAdmissionApplicability
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationAdmissionDecision (..)
  , QualificationAdmissionRevision
  , QualificationClaimRevision
  )
import Phil.Core.ProviderQualificationTargetReuse
  ( ProviderTargetRealizationEvidence (..)
  , TargetRealizationEvidenceRevision
  , deriveTargetRealizationEvidenceRevision
  )
import Phil.Core.Static
  ( DefinitionRevision
  , InstanceRevision
  , InterfaceRevision
  , RealizationRevision
  )
import ProviderQualificationLineageTargetKernel
  ( AdmissionApplicabilityDecision (..)
  , decideAdmissionApplicabilityByFacts
  )

newtype ProviderRequirementOccurrenceKey = ProviderRequirementOccurrenceKey
  { unProviderRequirementOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact applicability statement saying where one already-accepted provider
-- admission may be selected. Symbols are retained only as nonsemantic metadata.
data ProviderConcreteAdmissionApplicability = ProviderConcreteAdmissionApplicability
  { providerApplicabilityAdmissionRevision :: QualificationAdmissionRevision
  , providerApplicabilityClaimRevision :: QualificationClaimRevision
  , providerApplicabilityTargetEvidenceRevision :: TargetRealizationEvidenceRevision
  , providerApplicabilityRequirementOccurrence :: ProviderRequirementOccurrenceKey
  , providerApplicabilityInstanceRevision :: InstanceRevision
  , providerApplicabilityRealizationRevision :: RealizationRevision
  , providerApplicabilityRequiredInterface :: InterfaceRevision
  , providerApplicabilityImplementationDefinition :: DefinitionRevision
  , providerApplicabilityTargetProfileRevision :: Text
  , providerApplicabilityArtifactRevision :: Text
  , providerApplicabilityRuntimeAbiRevision :: Text
  , providerApplicabilityExportedSymbols :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

-- | Provider choice actually selected by ArchitectureRealization.
data SelectedProviderRealization = SelectedProviderRealization
  { selectedProviderAdmissionRevision :: QualificationAdmissionRevision
  , selectedProviderTargetEvidenceRevision :: TargetRealizationEvidenceRevision
  , selectedProviderRequirementOccurrence :: ProviderRequirementOccurrenceKey
  , selectedProviderInstanceRevision :: InstanceRevision
  , selectedProviderRealizationRevision :: RealizationRevision
  , selectedProviderRequiredInterface :: InterfaceRevision
  , selectedProviderImplementationDefinition :: DefinitionRevision
  , selectedProviderTargetProfileRevision :: Text
  , selectedProviderArtifactRevision :: Text
  , selectedProviderRuntimeAbiRevision :: Text
  , selectedProviderExportedSymbols :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

data CheckedProviderAdmissionApplicability = CheckedProviderAdmissionApplicability
  { checkedProviderApplicabilityAdmissionRevision :: QualificationAdmissionRevision
  , checkedProviderApplicabilityClaimRevision :: QualificationClaimRevision
  , checkedProviderApplicabilityTargetEvidenceRevision :: TargetRealizationEvidenceRevision
  , checkedProviderApplicabilityRequirementOccurrence :: ProviderRequirementOccurrenceKey
  , checkedProviderApplicabilityInstanceRevision :: InstanceRevision
  , checkedProviderApplicabilityRealizationRevision :: RealizationRevision
  }
  deriving (Eq, Ord, Show)

data ProviderAdmissionApplicabilityError
  = ProviderApplicabilityAdmissionRejected
  | ProviderApplicabilityAdmissionRevisionMismatch
      QualificationAdmissionRevision QualificationAdmissionRevision
  | ProviderApplicabilityClaimRevisionMismatch
      QualificationClaimRevision QualificationClaimRevision
  | ProviderApplicabilityTargetEvidenceRevisionMismatch
      TargetRealizationEvidenceRevision TargetRealizationEvidenceRevision
  | ProviderApplicabilityTargetEvidenceClaimMismatch
      QualificationClaimRevision QualificationClaimRevision
  | ProviderApplicabilityInterfaceMismatch InterfaceRevision InterfaceRevision
  | ProviderApplicabilityImplementationMismatch DefinitionRevision DefinitionRevision
  | ProviderApplicabilityTargetProfileMismatch Text Text
  | ProviderApplicabilityArtifactMismatch Text Text
  | ProviderApplicabilityRuntimeAbiMismatch Text Text
  | ProviderApplicabilityRequirementOccurrenceMismatch
      ProviderRequirementOccurrenceKey ProviderRequirementOccurrenceKey
  | ProviderApplicabilityInstanceRevisionMismatch InstanceRevision InstanceRevision
  | ProviderApplicabilityRealizationRevisionMismatch RealizationRevision RealizationRevision
  | ProviderApplicabilitySelectionAdmissionMismatch
      QualificationAdmissionRevision QualificationAdmissionRevision
  | ProviderApplicabilitySelectionTargetEvidenceMismatch
      TargetRealizationEvidenceRevision TargetRealizationEvidenceRevision
  deriving (Eq, Ord, Show)

checkProviderAdmissionApplicability
  :: CheckedProviderQualificationAdmissionIdentity
  -> ProviderTargetRealizationEvidence
  -> ProviderConcreteAdmissionApplicability
  -> SelectedProviderRealization
  -> Either ProviderAdmissionApplicabilityError CheckedProviderAdmissionApplicability
checkProviderAdmissionApplicability admission targetEvidence applicability selected =
  case decision of
    AdmissionApplicabilityAcceptedDecision ->
      Right CheckedProviderAdmissionApplicability
        { checkedProviderApplicabilityAdmissionRevision = expectedAdmission
        , checkedProviderApplicabilityClaimRevision = expectedClaim
        , checkedProviderApplicabilityTargetEvidenceRevision = expectedTargetEvidence
        , checkedProviderApplicabilityRequirementOccurrence =
            providerApplicabilityRequirementOccurrence applicability
        , checkedProviderApplicabilityInstanceRevision =
            providerApplicabilityInstanceRevision applicability
        , checkedProviderApplicabilityRealizationRevision =
            providerApplicabilityRealizationRevision applicability
        }
    AdmissionApplicabilityRejectedDecision ->
      Left ProviderApplicabilityAdmissionRejected
    AdmissionApplicabilityAdmissionRevisionDecision ->
      Left (ProviderApplicabilityAdmissionRevisionMismatch
        expectedAdmission (providerApplicabilityAdmissionRevision applicability))
    AdmissionApplicabilityClaimRevisionDecision ->
      Left (ProviderApplicabilityClaimRevisionMismatch
        expectedClaim (providerApplicabilityClaimRevision applicability))
    AdmissionApplicabilityTargetEvidenceRevisionDecision ->
      Left (ProviderApplicabilityTargetEvidenceRevisionMismatch
        expectedTargetEvidence (providerApplicabilityTargetEvidenceRevision applicability))
    AdmissionApplicabilityTargetEvidenceClaimDecision ->
      Left (ProviderApplicabilityTargetEvidenceClaimMismatch
        expectedClaim (targetEvidenceClaimRevision targetEvidence))
    AdmissionApplicabilityInterfaceEvidenceDecision ->
      Left (ProviderApplicabilityInterfaceMismatch
        (targetEvidenceRequiredInterface targetEvidence)
        (providerApplicabilityRequiredInterface applicability))
    AdmissionApplicabilityImplementationEvidenceDecision ->
      Left (ProviderApplicabilityImplementationMismatch
        (targetEvidenceSemanticImplementation targetEvidence)
        (providerApplicabilityImplementationDefinition applicability))
    AdmissionApplicabilityTargetEvidenceDecision ->
      Left (ProviderApplicabilityTargetProfileMismatch
        (targetEvidenceTargetProfileRevision targetEvidence)
        (providerApplicabilityTargetProfileRevision applicability))
    AdmissionApplicabilityArtifactEvidenceDecision ->
      Left (ProviderApplicabilityArtifactMismatch
        (targetEvidenceArtifactRevision targetEvidence)
        (providerApplicabilityArtifactRevision applicability))
    AdmissionApplicabilityAbiEvidenceDecision ->
      Left (ProviderApplicabilityRuntimeAbiMismatch
        (targetEvidenceRuntimeAbiRevision targetEvidence)
        (providerApplicabilityRuntimeAbiRevision applicability))
    AdmissionApplicabilitySelectedAdmissionDecision ->
      Left (ProviderApplicabilitySelectionAdmissionMismatch
        (providerApplicabilityAdmissionRevision applicability)
        (selectedProviderAdmissionRevision selected))
    AdmissionApplicabilitySelectedEvidenceDecision ->
      Left (ProviderApplicabilitySelectionTargetEvidenceMismatch
        (providerApplicabilityTargetEvidenceRevision applicability)
        (selectedProviderTargetEvidenceRevision selected))
    AdmissionApplicabilitySelectedOccurrenceDecision ->
      Left (ProviderApplicabilityRequirementOccurrenceMismatch
        (providerApplicabilityRequirementOccurrence applicability)
        (selectedProviderRequirementOccurrence selected))
    AdmissionApplicabilitySelectedInstanceDecision ->
      Left (ProviderApplicabilityInstanceRevisionMismatch
        (providerApplicabilityInstanceRevision applicability)
        (selectedProviderInstanceRevision selected))
    AdmissionApplicabilitySelectedRealizationDecision ->
      Left (ProviderApplicabilityRealizationRevisionMismatch
        (providerApplicabilityRealizationRevision applicability)
        (selectedProviderRealizationRevision selected))
    AdmissionApplicabilitySelectedInterfaceDecision ->
      Left (ProviderApplicabilityInterfaceMismatch
        (providerApplicabilityRequiredInterface applicability)
        (selectedProviderRequiredInterface selected))
    AdmissionApplicabilitySelectedImplementationDecision ->
      Left (ProviderApplicabilityImplementationMismatch
        (providerApplicabilityImplementationDefinition applicability)
        (selectedProviderImplementationDefinition selected))
    AdmissionApplicabilitySelectedTargetDecision ->
      Left (ProviderApplicabilityTargetProfileMismatch
        (providerApplicabilityTargetProfileRevision applicability)
        (selectedProviderTargetProfileRevision selected))
    AdmissionApplicabilitySelectedArtifactDecision ->
      Left (ProviderApplicabilityArtifactMismatch
        (providerApplicabilityArtifactRevision applicability)
        (selectedProviderArtifactRevision selected))
    AdmissionApplicabilitySelectedAbiDecision ->
      Left (ProviderApplicabilityRuntimeAbiMismatch
        (providerApplicabilityRuntimeAbiRevision applicability)
        (selectedProviderRuntimeAbiRevision selected))
  where
    expectedAdmission = checkedQualificationAdmissionRevision admission
    expectedClaim = checkedQualificationAdmissionClaimRevision admission
    expectedTargetEvidence = deriveTargetRealizationEvidenceRevision targetEvidence
    admitted = case checkedQualificationAdmissionDecision admission of
      QualificationAdmitted -> True
      QualificationRejected _ -> False
    decision = decideAdmissionApplicabilityByFacts
      admitted
      (providerApplicabilityAdmissionRevision applicability == expectedAdmission)
      (providerApplicabilityClaimRevision applicability == expectedClaim)
      (providerApplicabilityTargetEvidenceRevision applicability == expectedTargetEvidence)
      (targetEvidenceClaimRevision targetEvidence == expectedClaim)
      (providerApplicabilityRequiredInterface applicability ==
        targetEvidenceRequiredInterface targetEvidence)
      (providerApplicabilityImplementationDefinition applicability ==
        targetEvidenceSemanticImplementation targetEvidence)
      (providerApplicabilityTargetProfileRevision applicability ==
        targetEvidenceTargetProfileRevision targetEvidence)
      (providerApplicabilityArtifactRevision applicability ==
        targetEvidenceArtifactRevision targetEvidence)
      (providerApplicabilityRuntimeAbiRevision applicability ==
        targetEvidenceRuntimeAbiRevision targetEvidence)
      (selectedProviderAdmissionRevision selected ==
        providerApplicabilityAdmissionRevision applicability)
      (selectedProviderTargetEvidenceRevision selected ==
        providerApplicabilityTargetEvidenceRevision applicability)
      (selectedProviderRequirementOccurrence selected ==
        providerApplicabilityRequirementOccurrence applicability)
      (selectedProviderInstanceRevision selected ==
        providerApplicabilityInstanceRevision applicability)
      (selectedProviderRealizationRevision selected ==
        providerApplicabilityRealizationRevision applicability)
      (selectedProviderRequiredInterface selected ==
        providerApplicabilityRequiredInterface applicability)
      (selectedProviderImplementationDefinition selected ==
        providerApplicabilityImplementationDefinition applicability)
      (selectedProviderTargetProfileRevision selected ==
        providerApplicabilityTargetProfileRevision applicability)
      (selectedProviderArtifactRevision selected ==
        providerApplicabilityArtifactRevision applicability)
      (selectedProviderRuntimeAbiRevision selected ==
        providerApplicabilityRuntimeAbiRevision applicability)
