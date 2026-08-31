module Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericRequirementCategory
  , grammarV1GenericRequirementCompetence
  ) where

import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence
  , competenceForRequirementCategory
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1GenericRequirement (..))

-- | Preserve the source-selected generic requirement category exactly.
-- This is the first bounded Grammar-v1 -> semantic elaboration bridge for
-- SURF-008: it does not inspect payload shape to guess a different category.
grammarV1GenericRequirementCategory
  :: GrammarV1GenericRequirement
  -> GenericRequirementCategory
grammarV1GenericRequirementCategory requirement = case requirement of
  GrammarV1StructuralRequirement {} -> GenericStructuralCategory
  GrammarV1PropositionRequirement {} -> GenericPropositionCategory
  GrammarV1ProviderRequirement {} -> GenericProviderCategory
  GrammarV1CallableRequirement {} -> GenericCallableCategory
  GrammarV1BoundaryRequirement {} -> GenericBoundaryCategory
  GrammarV1ArchitectureRequirement {} -> GenericArchitectureCategory
  GrammarV1EffectsRequirement {} -> GenericEffectsCategory
  GrammarV1AuthorityRequirement {} -> GenericAuthorityCategory
  GrammarV1BoundaryRepresentationRequirement {} -> GenericBoundaryRepresentationCategory
  GrammarV1RepresentationRequirement {} -> GenericRepresentationCategory
  GrammarV1PlacementRequirement {} -> GenericPlacementCategory
  GrammarV1CostRequirement {} -> GenericCostCategory
  GrammarV1EnvironmentRequirement {} -> GenericEnvironmentCategory

-- | Route only through the checker competent for the preserved category.
grammarV1GenericRequirementCompetence
  :: GrammarV1GenericRequirement
  -> GenericRequirementCompetence
grammarV1GenericRequirementCompetence =
  competenceForRequirementCategory . grammarV1GenericRequirementCategory
