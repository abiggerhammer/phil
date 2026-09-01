module Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericRequirementCategory
  , grammarV1GenericRequirementCompetence
  , grammarV1GenericKindCategory
  , grammarV1BareStaticReferenceActual
  , grammarV1StructuralMode
  , grammarV1RelationProposition
  , grammarV1LogicalProposition
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
import Phil.Core.Syntax
  ( Mode (..)
  , Proposition (..)
  , RefTerm
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericKind (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RelationOperator (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1StructuralMode (..)
  )
import Phil.Surface.Syntax (Located (..))

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
          parts -> Just (ReferencedGenericStaticActual (Text.intercalate (Text.singleton '.') parts))
  _ -> Nothing

-- | Preserve an explicit source structural-mode choice exactly. Omission is
-- represented by the declaration's surrounding Maybe and must remain omitted
-- until the competent data/capability/closure mode checker derives or validates
-- the semantic mode; this mapping never invents a default.
grammarV1StructuralMode :: GrammarV1StructuralMode -> Mode
grammarV1StructuralMode sourceMode = case sourceMode of
  GrammarV1Unrestricted -> Unrestricted
  GrammarV1Affine -> Affine
  GrammarV1Linear -> Linear

-- | Route one already-parsed Grammar-v1 relation operator to its exact Core
-- proposition constructor. Greater-than relations canonicalize by reversing
-- operands into Core's LessThan/LessEqual forms; membership and disjointness
-- remain their native semantic propositions. No relation is retried as another
-- category to obtain acceptance.
grammarV1RelationProposition
  :: GrammarV1RelationOperator
  -> RefTerm
  -> RefTerm
  -> Proposition
grammarV1RelationProposition operator left right = case operator of
  GrammarV1EqualRelation -> Equal left right
  GrammarV1NotEqualRelation -> NotEqual left right
  GrammarV1LessEqualRelation -> LessEqual left right
  GrammarV1GreaterEqualRelation -> LessEqual right left
  GrammarV1LessRelation -> LessThan left right
  GrammarV1GreaterRelation -> LessThan right left
  GrammarV1InRelation -> Member left right
  GrammarV1DisjointRelation -> Disjoint left right

-- | Preserve the parser-selected logical connective tree exactly for the
-- proposition fragment whose leaves are intrinsic truth values. Atomic relation
-- and claim-application leaves remain owned by their competent elaborators and
-- therefore fail closed at this bounded bridge instead of being reinterpreted.
grammarV1LogicalProposition :: GrammarV1Proposition -> Maybe Proposition
grammarV1LogicalProposition source = case source of
  GrammarV1TrueProposition -> Just Truth
  GrammarV1FalseProposition -> Just Falsehood
  GrammarV1NotProposition (Located _ inner) ->
    Negation <$> grammarV1LogicalProposition inner
  GrammarV1AndProposition (Located _ left) (Located _ right) ->
    Conjunction
      <$> grammarV1LogicalProposition left
      <*> grammarV1LogicalProposition right
  GrammarV1OrProposition (Located _ left) (Located _ right) ->
    Disjunction
      <$> grammarV1LogicalProposition left
      <*> grammarV1LogicalProposition right
  _ -> Nothing
