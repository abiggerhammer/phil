{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Generic.RequirementCategory
  ( GenericRequirementKey (..)
  , GenericRequirementCategory (..)
  , GenericRequirementCompetence (..)
  , GenericPublicRequirement (..)
  , GenericRequirementHandoffTarget (..)
  , GenericRequirementHandoff (..)
  , CheckedGenericRequirementHandoff (..)
  , CheckedGenericRequirementInterface (..)
  , GenericRequirementCategoryError (..)
  , competenceForRequirementCategory
  , checkGenericRequirementHandoffs
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (SemanticForm)

newtype GenericRequirementKey = GenericRequirementKey
  { unGenericRequirementKey :: Text
  }
  deriving (Eq, Ord, Show)

data GenericRequirementCategory
  = GenericStructuralCategory
  | GenericPropositionCategory
  | GenericProviderCategory
  | GenericCallableCategory
  | GenericBoundaryCategory
  | GenericArchitectureCategory
  | GenericEffectsCategory
  | GenericAuthorityCategory
  | GenericBoundaryRepresentationCategory
  | GenericRepresentationCategory
  | GenericPlacementCategory
  | GenericCostCategory
  | GenericEnvironmentCategory
  deriving (Eq, Ord, Show)

data GenericRequirementCompetence
  = StructuralRequirementChecker
  | PropositionRequirementChecker
  | ProviderRequirementChecker
  | CallableRequirementChecker
  | BoundaryRequirementChecker
  | ArchitectureRequirementChecker
  | EffectsRequirementChecker
  | AuthorityRequirementChecker
  | BoundaryRepresentationRequirementChecker
  | RepresentationRequirementChecker
  | PlacementRequirementChecker
  | CostRequirementChecker
  | EnvironmentRequirementChecker
  deriving (Eq, Ord, Show)

data GenericPublicRequirement = GenericPublicRequirement
  { genericPublicRequirementKey :: GenericRequirementKey
  , genericPublicRequirementCategory :: GenericRequirementCategory
  , genericPublicRequirementSemanticForm :: SemanticForm
  }
  deriving (Eq, Ord, Show)

-- | Handoff targets model the output of elaboration before it is trusted. An
-- implementation may request the checker competent for one semantic category,
-- or it may incorrectly attempt to turn the requirement into an assumption.
-- Generic interface checking rejects the latter; any later assumption
-- disposition belongs to an explicitly permitted enclosing assurance boundary.
data GenericRequirementHandoffTarget
  = GenericHandoffToCompetence GenericRequirementCompetence
  | GenericHandoffAsAssumption Text
  deriving (Eq, Ord, Show)

data GenericRequirementHandoff = GenericRequirementHandoff
  { genericHandoffRequirementKey :: GenericRequirementKey
  , genericHandoffRequirementCategory :: GenericRequirementCategory
  , genericHandoffTarget :: GenericRequirementHandoffTarget
  }
  deriving (Eq, Ord, Show)

data CheckedGenericRequirementHandoff = CheckedGenericRequirementHandoff
  { checkedRequirementKey :: GenericRequirementKey
  , checkedRequirementCategory :: GenericRequirementCategory
  , checkedRequirementSemanticForm :: SemanticForm
  , checkedRequirementCompetence :: GenericRequirementCompetence
  }
  deriving (Eq, Ord, Show)

newtype CheckedGenericRequirementInterface = CheckedGenericRequirementInterface
  { checkedGenericRequirementHandoffs
      :: Map.Map GenericRequirementKey CheckedGenericRequirementHandoff
  }
  deriving (Eq, Show)

data GenericRequirementCategoryError
  = DuplicateGenericPublicRequirement GenericRequirementKey
  | DuplicateGenericRequirementHandoff GenericRequirementKey
  | MissingGenericRequirementHandoff GenericRequirementKey
  | UnexpectedGenericRequirementHandoff GenericRequirementKey
  | GenericRequirementCategorySubstitution
      GenericRequirementKey
      GenericRequirementCategory
      GenericRequirementCategory
  | GenericRequirementCompetenceMismatch
      GenericRequirementKey
      GenericRequirementCategory
      GenericRequirementCompetence
      GenericRequirementCompetence
  | GenericRequirementSilentAssumption
      GenericRequirementKey
      GenericRequirementCategory
      Text
  deriving (Eq, Show)

competenceForRequirementCategory
  :: GenericRequirementCategory
  -> GenericRequirementCompetence
competenceForRequirementCategory category = case category of
  GenericStructuralCategory -> StructuralRequirementChecker
  GenericPropositionCategory -> PropositionRequirementChecker
  GenericProviderCategory -> ProviderRequirementChecker
  GenericCallableCategory -> CallableRequirementChecker
  GenericBoundaryCategory -> BoundaryRequirementChecker
  GenericArchitectureCategory -> ArchitectureRequirementChecker
  GenericEffectsCategory -> EffectsRequirementChecker
  GenericAuthorityCategory -> AuthorityRequirementChecker
  GenericBoundaryRepresentationCategory -> BoundaryRepresentationRequirementChecker
  GenericRepresentationCategory -> RepresentationRequirementChecker
  GenericPlacementCategory -> PlacementRequirementChecker
  GenericCostCategory -> CostRequirementChecker
  GenericEnvironmentCategory -> EnvironmentRequirementChecker

checkGenericRequirementHandoffs
  :: [GenericPublicRequirement]
  -> [GenericRequirementHandoff]
  -> Either GenericRequirementCategoryError CheckedGenericRequirementInterface
checkGenericRequirementHandoffs requirements handoffs = do
  requirementMap <- normalizeRequirements requirements
  handoffMap <- normalizeHandoffs handoffs
  case Set.lookupMin (Map.keysSet requirementMap `Set.difference` Map.keysSet handoffMap) of
    Just key -> Left (MissingGenericRequirementHandoff key)
    Nothing -> Right ()
  case Set.lookupMin (Map.keysSet handoffMap `Set.difference` Map.keysSet requirementMap) of
    Just key -> Left (UnexpectedGenericRequirementHandoff key)
    Nothing -> Right ()
  checked <- Map.traverseWithKey (checkOne handoffMap) requirementMap
  pure (CheckedGenericRequirementInterface checked)

normalizeRequirements
  :: [GenericPublicRequirement]
  -> Either GenericRequirementCategoryError
      (Map.Map GenericRequirementKey GenericPublicRequirement)
normalizeRequirements = foldl' insertOne (Right Map.empty)
  where
    insertOne accumulated requirement = do
      current <- accumulated
      let key = genericPublicRequirementKey requirement
      if Map.member key current
        then Left (DuplicateGenericPublicRequirement key)
        else Right (Map.insert key requirement current)

normalizeHandoffs
  :: [GenericRequirementHandoff]
  -> Either GenericRequirementCategoryError
      (Map.Map GenericRequirementKey GenericRequirementHandoff)
normalizeHandoffs = foldl' insertOne (Right Map.empty)
  where
    insertOne accumulated handoff = do
      current <- accumulated
      let key = genericHandoffRequirementKey handoff
      if Map.member key current
        then Left (DuplicateGenericRequirementHandoff key)
        else Right (Map.insert key handoff current)

checkOne
  :: Map.Map GenericRequirementKey GenericRequirementHandoff
  -> GenericRequirementKey
  -> GenericPublicRequirement
  -> Either GenericRequirementCategoryError CheckedGenericRequirementHandoff
checkOne handoffs key requirement = do
  handoff <- maybe
    (Left (MissingGenericRequirementHandoff key))
    Right
    (Map.lookup key handoffs)
  let expectedCategory = genericPublicRequirementCategory requirement
      actualCategory = genericHandoffRequirementCategory handoff
  if actualCategory == expectedCategory
    then Right ()
    else Left (GenericRequirementCategorySubstitution
      key expectedCategory actualCategory)
  competence <- case genericHandoffTarget handoff of
    GenericHandoffAsAssumption detail ->
      Left (GenericRequirementSilentAssumption key expectedCategory detail)
    GenericHandoffToCompetence actualCompetence -> do
      let expectedCompetence = competenceForRequirementCategory expectedCategory
      if actualCompetence == expectedCompetence
        then Right actualCompetence
        else Left (GenericRequirementCompetenceMismatch
          key expectedCategory expectedCompetence actualCompetence)
  pure CheckedGenericRequirementHandoff
    { checkedRequirementKey = key
    , checkedRequirementCategory = expectedCategory
    , checkedRequirementSemanticForm = genericPublicRequirementSemanticForm requirement
    , checkedRequirementCompetence = competence
    }
