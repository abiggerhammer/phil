module Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericRequirementCategory
  , grammarV1GenericRequirementCompetence
  , grammarV1GenericKindCategory
  , grammarV1BareStaticReferenceActual
  ) where

import qualified Data.Text as Text
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence
  , competenceForRequirementCategory
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericKind (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  )

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

-- | Preserve the declared generic parameter kind exactly for GEN-013.
-- Contract-bearing kinds retain their semantic category; their contract type
-- payload is checked by the competent semantic layer rather than being used to
-- reinterpret the kind.
grammarV1GenericKindCategory :: GrammarV1GenericKind -> GenericStaticKind
grammarV1GenericKindCategory kind = case kind of
  GrammarV1TypeKind -> GenericTypeKind
  GrammarV1NatKind -> GenericIndexKind
  GrammarV1SessionKind -> GenericSessionKind
  GrammarV1MessageKind -> GenericMessageKind
  GrammarV1EffectsKind -> GenericEffectsKind
  GrammarV1ProviderKind _ -> GenericProviderContractKind
  GrammarV1CallableKind _ -> GenericCallableContractKind
  GrammarV1BoundaryKind _ -> GenericBoundaryContractKind
  GrammarV1ArchitectureKind _ -> GenericArchitectureDependencyKind

-- | A bare name-shaped static actual remains one unresolved reference. Its
-- semantic category is selected only by the declared parameter kind in GEN-013;
-- this bridge never guesses a kind from the reference spelling or candidates.
-- Specialized references remain fail-closed for a later exact-reference slice.
grammarV1BareStaticReferenceActual
  :: GrammarV1StaticArgument
  -> Maybe GenericStaticActual
grammarV1BareStaticReferenceActual argument = case argument of
  GrammarV1StaticReferenceArgument reference
    | null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts -> Just (ReferencedGenericStaticActual (Text.intercalate "." parts))
  _ -> Nothing
