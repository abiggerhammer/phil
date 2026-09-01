{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProviderQualificationTargetReuse
  ( TargetRealizationEvidenceRevision (..)
  , ProviderTargetRealizationEvidence (..)
  , CheckedProviderCrossTargetReuse (..)
  , ProviderCrossTargetReuseError (..)
  , deriveTargetRealizationEvidenceRevision
  , checkProviderCrossTargetSemanticReuse
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationClaimIdentityInput (..)
  , ProviderQualificationLayer (..)
  , ProviderQualificationSubject (..)
  , QualificationClaimRevision (..)
  , deriveQualificationClaimRevision
  )
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import ProviderQualificationLineageTargetKernel
  ( TargetReuseDecision (..)
  , decideTargetReuseByFacts
  )

newtype TargetRealizationEvidenceRevision = TargetRealizationEvidenceRevision
  { unTargetRealizationEvidenceRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Target-specific evidence layered below one reusable semantic provider claim.
-- Semantic operation/state/law/authority/evidence-competence facts stay in the
-- claim revision; concrete artifact, ABI, realization, translation, and target
-- assumptions live here and must be rebound for each target.
data ProviderTargetRealizationEvidence = ProviderTargetRealizationEvidence
  { targetEvidenceClaimRevision :: QualificationClaimRevision
  , targetEvidenceRequiredInterface :: InterfaceRevision
  , targetEvidenceSemanticImplementation :: DefinitionRevision
  , targetEvidenceTargetProfileRevision :: Text
  , targetEvidenceArtifactRevision :: Text
  , targetEvidenceRuntimeAbiRevision :: Text
  , targetEvidenceRealizationRelationRevision :: Text
  , targetEvidenceTranslationValidationRefs :: Set.Set Text
  , targetEvidenceTargetAssumptions :: Set.Set Text
  }
  deriving (Eq, Ord, Show)

data CheckedProviderCrossTargetReuse = CheckedProviderCrossTargetReuse
  { checkedCrossTargetClaimRevision :: QualificationClaimRevision
  , checkedCrossTargetSemanticImplementation :: DefinitionRevision
  , checkedCrossTargetPriorEvidenceRevision :: TargetRealizationEvidenceRevision
  , checkedCrossTargetNewEvidenceRevision :: TargetRealizationEvidenceRevision
  , checkedCrossTargetPriorTargetProfile :: Text
  , checkedCrossTargetNewTargetProfile :: Text
  }
  deriving (Eq, Ord, Show)

data ProviderCrossTargetReuseError
  = TargetReuseRequiresSemanticImplementationClaim
  | TargetReuseClaimRevisionMismatch QualificationClaimRevision QualificationClaimRevision
  | TargetReuseInterfaceMismatch InterfaceRevision InterfaceRevision
  | TargetReuseImplementationMismatch DefinitionRevision DefinitionRevision
  | TargetReuseRequiresDistinctTarget Text
  | TargetReuseMissingTranslationEvidence Text
  deriving (Eq, Ord, Show)

deriveTargetRealizationEvidenceRevision
  :: ProviderTargetRealizationEvidence
  -> TargetRealizationEvidenceRevision
deriveTargetRealizationEvidenceRevision evidence = TargetRealizationEvidenceRevision
  ("phil.provider-qualification.target-evidence.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("claim_revision", SemanticAtom
          (unQualificationClaimRevision (targetEvidenceClaimRevision evidence)))
      , ("required_interface", SemanticAtom
          (unInterfaceRevision (targetEvidenceRequiredInterface evidence)))
      , ("semantic_implementation", SemanticAtom
          (unDefinitionRevision (targetEvidenceSemanticImplementation evidence)))
      , ("target_profile", SemanticAtom (targetEvidenceTargetProfileRevision evidence))
      , ("artifact_revision", SemanticAtom (targetEvidenceArtifactRevision evidence))
      , ("runtime_abi_revision", SemanticAtom (targetEvidenceRuntimeAbiRevision evidence))
      , ("realization_relation_revision", SemanticAtom
          (targetEvidenceRealizationRelationRevision evidence))
      , ("translation_validation_refs", SemanticUnordered
          (Set.map SemanticAtom (targetEvidenceTranslationValidationRefs evidence)))
      , ("target_assumptions", SemanticUnordered
          (Set.map SemanticAtom (targetEvidenceTargetAssumptions evidence)))
      ])))

checkProviderCrossTargetSemanticReuse
  :: ProviderQualificationClaimIdentityInput
  -> ProviderTargetRealizationEvidence
  -> ProviderTargetRealizationEvidence
  -> Either ProviderCrossTargetReuseError CheckedProviderCrossTargetReuse
checkProviderCrossTargetSemanticReuse claim priorEvidence newEvidence =
  case decision of
    TargetReuseAcceptedDecision ->
      case semanticImplementation of
        Just implementation -> Right CheckedProviderCrossTargetReuse
          { checkedCrossTargetClaimRevision = claimRevision
          , checkedCrossTargetSemanticImplementation = implementation
          , checkedCrossTargetPriorEvidenceRevision =
              deriveTargetRealizationEvidenceRevision priorEvidence
          , checkedCrossTargetNewEvidenceRevision =
              deriveTargetRealizationEvidenceRevision newEvidence
          , checkedCrossTargetPriorTargetProfile =
              targetEvidenceTargetProfileRevision priorEvidence
          , checkedCrossTargetNewTargetProfile =
              targetEvidenceTargetProfileRevision newEvidence
          }
        Nothing -> Left TargetReuseRequiresSemanticImplementationClaim
    TargetReuseSemanticLayerDecision ->
      Left TargetReuseRequiresSemanticImplementationClaim
    TargetReuseSemanticSubjectDecision ->
      Left TargetReuseRequiresSemanticImplementationClaim
    TargetReusePriorClaimDecision ->
      Left (TargetReuseClaimRevisionMismatch
        claimRevision (targetEvidenceClaimRevision priorEvidence))
    TargetReusePriorInterfaceDecision ->
      Left (TargetReuseInterfaceMismatch
        requiredInterface (targetEvidenceRequiredInterface priorEvidence))
    TargetReusePriorImplementationDecision ->
      case semanticImplementation of
        Just implementation -> Left (TargetReuseImplementationMismatch
          implementation (targetEvidenceSemanticImplementation priorEvidence))
        Nothing -> Left TargetReuseRequiresSemanticImplementationClaim
    TargetReusePriorTranslationDecision ->
      Left (TargetReuseMissingTranslationEvidence
        (targetEvidenceTargetProfileRevision priorEvidence))
    TargetReuseNewClaimDecision ->
      Left (TargetReuseClaimRevisionMismatch
        claimRevision (targetEvidenceClaimRevision newEvidence))
    TargetReuseNewInterfaceDecision ->
      Left (TargetReuseInterfaceMismatch
        requiredInterface (targetEvidenceRequiredInterface newEvidence))
    TargetReuseNewImplementationDecision ->
      case semanticImplementation of
        Just implementation -> Left (TargetReuseImplementationMismatch
          implementation (targetEvidenceSemanticImplementation newEvidence))
        Nothing -> Left TargetReuseRequiresSemanticImplementationClaim
    TargetReuseNewTranslationDecision ->
      Left (TargetReuseMissingTranslationEvidence
        (targetEvidenceTargetProfileRevision newEvidence))
    TargetReuseDistinctProfileDecision ->
      Left (TargetReuseRequiresDistinctTarget
        (targetEvidenceTargetProfileRevision newEvidence))
  where
    claimRevision = deriveQualificationClaimRevision claim
    requiredInterface = qualificationClaimRequiredInterface claim
    semanticLayer = qualificationClaimLayer claim == SemanticImplementationQualification
    semanticImplementation = case qualificationClaimSubject claim of
      SemanticProviderImplementation revision -> Just revision
      _ -> Nothing
    semanticSubject = case semanticImplementation of
      Just _ -> True
      Nothing -> False
    implementationMatches evidence = case semanticImplementation of
      Just implementation -> targetEvidenceSemanticImplementation evidence == implementation
      Nothing -> False
    decision = decideTargetReuseByFacts
      semanticLayer
      semanticSubject
      (targetEvidenceClaimRevision priorEvidence == claimRevision)
      (targetEvidenceRequiredInterface priorEvidence == requiredInterface)
      (implementationMatches priorEvidence)
      (not (Set.null (targetEvidenceTranslationValidationRefs priorEvidence)))
      (targetEvidenceClaimRevision newEvidence == claimRevision)
      (targetEvidenceRequiredInterface newEvidence == requiredInterface)
      (implementationMatches newEvidence)
      (not (Set.null (targetEvidenceTranslationValidationRefs newEvidence)))
      (targetEvidenceTargetProfileRevision priorEvidence /=
        targetEvidenceTargetProfileRevision newEvidence)
