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
  , QualificationClaimRevision
  , deriveQualificationClaimRevision
  )
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
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
          (showClaimRevision (targetEvidenceClaimRevision evidence)))
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
  where
    showClaimRevision = \revision -> case show revision of
      rendered -> fromStringShow rendered

    -- QualificationClaimRevision deliberately keeps its constructor field
    -- abstract from this module's import list. Show is stable only for this
    -- inspectable Phase 1 identity substrate; compact serialization remains
    -- deferred and must preserve the same equality relation.
    fromStringShow = Data.Text.pack

checkProviderCrossTargetSemanticReuse
  :: ProviderQualificationClaimIdentityInput
  -> ProviderTargetRealizationEvidence
  -> ProviderTargetRealizationEvidence
  -> Either ProviderCrossTargetReuseError CheckedProviderCrossTargetReuse
checkProviderCrossTargetSemanticReuse claim priorEvidence newEvidence = do
  implementation <- semanticImplementation
  let claimRevision = deriveQualificationClaimRevision claim
      requiredInterface = qualificationClaimRequiredInterface claim
  validateEvidence claimRevision requiredInterface implementation priorEvidence
  validateEvidence claimRevision requiredInterface implementation newEvidence
  if targetEvidenceTargetProfileRevision priorEvidence ==
      targetEvidenceTargetProfileRevision newEvidence
    then Left (TargetReuseRequiresDistinctTarget
      (targetEvidenceTargetProfileRevision newEvidence))
    else if Set.null (targetEvidenceTranslationValidationRefs newEvidence)
      then Left (TargetReuseMissingTranslationEvidence
        (targetEvidenceTargetProfileRevision newEvidence))
      else Right CheckedProviderCrossTargetReuse
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
  where
    semanticImplementation = case
      (qualificationClaimLayer claim, qualificationClaimSubject claim) of
      (SemanticImplementationQualification, SemanticProviderImplementation revision) ->
        Right revision
      _ -> Left TargetReuseRequiresSemanticImplementationClaim

    validateEvidence claimRevision requiredInterface implementation evidence
      | targetEvidenceClaimRevision evidence /= claimRevision =
          Left (TargetReuseClaimRevisionMismatch
            claimRevision (targetEvidenceClaimRevision evidence))
      | targetEvidenceRequiredInterface evidence /= requiredInterface =
          Left (TargetReuseInterfaceMismatch
            requiredInterface (targetEvidenceRequiredInterface evidence))
      | targetEvidenceSemanticImplementation evidence /= implementation =
          Left (TargetReuseImplementationMismatch
            implementation (targetEvidenceSemanticImplementation evidence))
      | Set.null (targetEvidenceTranslationValidationRefs evidence) =
          Left (TargetReuseMissingTranslationEvidence
            (targetEvidenceTargetProfileRevision evidence))
      | otherwise = Right ()
