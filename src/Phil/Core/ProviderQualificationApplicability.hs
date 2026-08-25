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
checkProviderAdmissionApplicability admission targetEvidence applicability selected = do
  case checkedQualificationAdmissionDecision admission of
    QualificationAdmitted -> Right ()
    QualificationRejected _ -> Left ProviderApplicabilityAdmissionRejected
  let expectedAdmission = checkedQualificationAdmissionRevision admission
      expectedClaim = checkedQualificationAdmissionClaimRevision admission
      expectedTargetEvidence = deriveTargetRealizationEvidenceRevision targetEvidence
  requireEqual ProviderApplicabilityAdmissionRevisionMismatch
    expectedAdmission (providerApplicabilityAdmissionRevision applicability)
  requireEqual ProviderApplicabilityClaimRevisionMismatch
    expectedClaim (providerApplicabilityClaimRevision applicability)
  requireEqual ProviderApplicabilityTargetEvidenceRevisionMismatch
    expectedTargetEvidence (providerApplicabilityTargetEvidenceRevision applicability)
  requireEqual ProviderApplicabilityTargetEvidenceClaimMismatch
    expectedClaim (targetEvidenceClaimRevision targetEvidence)
  requireEqual ProviderApplicabilityInterfaceMismatch
    (targetEvidenceRequiredInterface targetEvidence)
    (providerApplicabilityRequiredInterface applicability)
  requireEqual ProviderApplicabilityImplementationMismatch
    (targetEvidenceSemanticImplementation targetEvidence)
    (providerApplicabilityImplementationDefinition applicability)
  requireEqual ProviderApplicabilityTargetProfileMismatch
    (targetEvidenceTargetProfileRevision targetEvidence)
    (providerApplicabilityTargetProfileRevision applicability)
  requireEqual ProviderApplicabilityArtifactMismatch
    (targetEvidenceArtifactRevision targetEvidence)
    (providerApplicabilityArtifactRevision applicability)
  requireEqual ProviderApplicabilityRuntimeAbiMismatch
    (targetEvidenceRuntimeAbiRevision targetEvidence)
    (providerApplicabilityRuntimeAbiRevision applicability)

  requireEqual ProviderApplicabilitySelectionAdmissionMismatch
    (providerApplicabilityAdmissionRevision applicability)
    (selectedProviderAdmissionRevision selected)
  requireEqual ProviderApplicabilitySelectionTargetEvidenceMismatch
    (providerApplicabilityTargetEvidenceRevision applicability)
    (selectedProviderTargetEvidenceRevision selected)
  requireEqual ProviderApplicabilityRequirementOccurrenceMismatch
    (providerApplicabilityRequirementOccurrence applicability)
    (selectedProviderRequirementOccurrence selected)
  requireEqual ProviderApplicabilityInstanceRevisionMismatch
    (providerApplicabilityInstanceRevision applicability)
    (selectedProviderInstanceRevision selected)
  requireEqual ProviderApplicabilityRealizationRevisionMismatch
    (providerApplicabilityRealizationRevision applicability)
    (selectedProviderRealizationRevision selected)
  requireEqual ProviderApplicabilityInterfaceMismatch
    (providerApplicabilityRequiredInterface applicability)
    (selectedProviderRequiredInterface selected)
  requireEqual ProviderApplicabilityImplementationMismatch
    (providerApplicabilityImplementationDefinition applicability)
    (selectedProviderImplementationDefinition selected)
  requireEqual ProviderApplicabilityTargetProfileMismatch
    (providerApplicabilityTargetProfileRevision applicability)
    (selectedProviderTargetProfileRevision selected)
  requireEqual ProviderApplicabilityArtifactMismatch
    (providerApplicabilityArtifactRevision applicability)
    (selectedProviderArtifactRevision selected)
  requireEqual ProviderApplicabilityRuntimeAbiMismatch
    (providerApplicabilityRuntimeAbiRevision applicability)
    (selectedProviderRuntimeAbiRevision selected)

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

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)
