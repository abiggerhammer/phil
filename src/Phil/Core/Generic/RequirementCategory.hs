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
import qualified Phil.Core.GenericRequirementCategoryKernelBridge as KernelBridge
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
  | GenericRequirementCategoryKernelDisagreement Text
  deriving (Eq, Show)

competenceForRequirementCategory
  :: GenericRequirementCategory
  -> GenericRequirementCompetence
competenceForRequirementCategory =
  fromKernelCompetence
    . KernelBridge.certifiedCompetenceForKernelCategory
    . toKernelCategory

checkGenericRequirementHandoffs
  :: [GenericPublicRequirement]
  -> [GenericRequirementHandoff]
  -> Either GenericRequirementCategoryError CheckedGenericRequirementInterface
checkGenericRequirementHandoffs requirements handoffs = do
  requirementMap <- normalizeRequirements requirements
  handoffMap <- normalizeHandoffs handoffs
  let requirementKeys = Map.keysSet requirementMap
      handoffKeys = Map.keysSet handoffMap
      handoffDomainExact = requirementKeys == handoffKeys
  case Set.lookupMin (requirementKeys `Set.difference` handoffKeys) of
    Just key -> do
      requireDomainClassification
        KernelBridge.RequirementInterfaceHandoffDomainClassification
        handoffDomainExact
        False
      Left (MissingGenericRequirementHandoff key)
    Nothing -> Right ()
  case Set.lookupMin (handoffKeys `Set.difference` requirementKeys) of
    Just key -> do
      requireDomainClassification
        KernelBridge.RequirementInterfaceHandoffDomainClassification
        handoffDomainExact
        False
      Left (UnexpectedGenericRequirementHandoff key)
    Nothing -> Right ()
  checked <- Map.traverseWithKey (checkOne handoffMap) requirementMap
  let checkedDomainExact = Map.keysSet checked == requirementKeys
  requireDomainClassification
    KernelBridge.RequirementInterfaceDomainAcceptedClassification
    handoffDomainExact
    checkedDomainExact
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
      handoffKeyMatches =
        genericHandoffRequirementKey handoff == genericPublicRequirementKey requirement
  if handoffKeyMatches
    then Right ()
    else do
      requireHandoffClassification
        KernelBridge.RequirementHandoffKeyClassification
        False False False False False False False
      Left (GenericRequirementCategoryKernelDisagreement
        "normalized handoff key did not match its public requirement key")
  if actualCategory == expectedCategory
    then Right ()
    else do
      requireHandoffClassification
        KernelBridge.RequirementHandoffCategoryClassification
        True False False False False False False
      Left (GenericRequirementCategorySubstitution
        key expectedCategory actualCategory)
  let expectedCompetence = competenceForRequirementCategory expectedCategory
  competence <- case genericHandoffTarget handoff of
    GenericHandoffAsAssumption detail -> do
      requireHandoffClassification
        KernelBridge.RequirementHandoffTargetClassification
        True True False False False False False
      Left (GenericRequirementSilentAssumption key expectedCategory detail)
    GenericHandoffToCompetence actualCompetence ->
      if actualCompetence == expectedCompetence
        then Right actualCompetence
        else do
          requireHandoffClassification
            KernelBridge.RequirementHandoffTargetClassification
            True True False False False False False
          Left (GenericRequirementCompetenceMismatch
            key expectedCategory expectedCompetence actualCompetence)
  let checked = CheckedGenericRequirementHandoff
        { checkedRequirementKey = key
        , checkedRequirementCategory = expectedCategory
        , checkedRequirementSemanticForm = genericPublicRequirementSemanticForm requirement
        , checkedRequirementCompetence = competence
        }
      targetMatches = case genericHandoffTarget handoff of
        GenericHandoffToCompetence actualCompetence ->
          actualCompetence == expectedCompetence
        GenericHandoffAsAssumption _ -> False
  requireHandoffClassification
    KernelBridge.RequirementHandoffAcceptedClassification
    handoffKeyMatches
    (actualCategory == expectedCategory)
    targetMatches
    (checkedRequirementKey checked == genericPublicRequirementKey requirement)
    (checkedRequirementCategory checked == expectedCategory)
    (checkedRequirementSemanticForm checked == genericPublicRequirementSemanticForm requirement)
    (checkedRequirementCompetence checked == expectedCompetence)
  pure checked

requireHandoffClassification
  :: KernelBridge.RequirementHandoffClassification
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Bool
  -> Either GenericRequirementCategoryError ()
requireHandoffClassification expected handoffKeyMatches handoffCategoryMatches
    handoffTargetMatches checkedKeyMatches checkedCategoryMatches
    checkedSemanticFormMatches checkedCompetenceMatches =
  let actual = KernelBridge.classifyRequirementHandoffFacts
        handoffKeyMatches
        handoffCategoryMatches
        handoffTargetMatches
        checkedKeyMatches
        checkedCategoryMatches
        checkedSemanticFormMatches
        checkedCompetenceMatches
  in if actual == expected
      then Right ()
      else Left (GenericRequirementCategoryKernelDisagreement
        "extracted handoff decision disagreed with native GEN-014 classification")

requireDomainClassification
  :: KernelBridge.RequirementInterfaceDomainClassification
  -> Bool
  -> Bool
  -> Either GenericRequirementCategoryError ()
requireDomainClassification expected handoffDomainExact checkedDomainExact =
  let actual = KernelBridge.classifyRequirementInterfaceDomainFacts
        handoffDomainExact checkedDomainExact
  in if actual == expected
      then Right ()
      else Left (GenericRequirementCategoryKernelDisagreement
        "extracted interface-domain decision disagreed with native GEN-014 classification")

toKernelCategory
  :: GenericRequirementCategory
  -> KernelBridge.KernelRequirementCategory
toKernelCategory category = case category of
  GenericStructuralCategory -> KernelBridge.KernelStructuralCategory
  GenericPropositionCategory -> KernelBridge.KernelPropositionCategory
  GenericProviderCategory -> KernelBridge.KernelProviderCategory
  GenericCallableCategory -> KernelBridge.KernelCallableCategory
  GenericBoundaryCategory -> KernelBridge.KernelBoundaryCategory
  GenericArchitectureCategory -> KernelBridge.KernelArchitectureCategory
  GenericEffectsCategory -> KernelBridge.KernelEffectsCategory
  GenericAuthorityCategory -> KernelBridge.KernelAuthorityCategory
  GenericBoundaryRepresentationCategory -> KernelBridge.KernelBoundaryRepresentationCategory
  GenericRepresentationCategory -> KernelBridge.KernelRepresentationCategory
  GenericPlacementCategory -> KernelBridge.KernelPlacementCategory
  GenericCostCategory -> KernelBridge.KernelCostCategory
  GenericEnvironmentCategory -> KernelBridge.KernelEnvironmentCategory

fromKernelCompetence
  :: KernelBridge.KernelRequirementCompetence
  -> GenericRequirementCompetence
fromKernelCompetence competence = case competence of
  KernelBridge.KernelStructuralRequirementChecker -> StructuralRequirementChecker
  KernelBridge.KernelPropositionRequirementChecker -> PropositionRequirementChecker
  KernelBridge.KernelProviderRequirementChecker -> ProviderRequirementChecker
  KernelBridge.KernelCallableRequirementChecker -> CallableRequirementChecker
  KernelBridge.KernelBoundaryRequirementChecker -> BoundaryRequirementChecker
  KernelBridge.KernelArchitectureRequirementChecker -> ArchitectureRequirementChecker
  KernelBridge.KernelEffectsRequirementChecker -> EffectsRequirementChecker
  KernelBridge.KernelAuthorityRequirementChecker -> AuthorityRequirementChecker
  KernelBridge.KernelBoundaryRepresentationRequirementChecker ->
    BoundaryRepresentationRequirementChecker
  KernelBridge.KernelRepresentationRequirementChecker -> RepresentationRequirementChecker
  KernelBridge.KernelPlacementRequirementChecker -> PlacementRequirementChecker
  KernelBridge.KernelCostRequirementChecker -> CostRequirementChecker
  KernelBridge.KernelEnvironmentRequirementChecker -> EnvironmentRequirementChecker
