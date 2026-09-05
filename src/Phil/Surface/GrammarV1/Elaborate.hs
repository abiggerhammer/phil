module Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericRequirementCategory
  , grammarV1GenericRequirementCompetence
  , grammarV1GenericKindCategory
  , grammarV1BareStaticReferenceActual
  , grammarV1StructuralMode
  , grammarV1RelationProposition
  , grammarV1LogicalProposition
  , grammarV1PrimitiveType
  , grammarV1IntrinsicRefLiteral
  , grammarV1IntrinsicBytesType
  , grammarV1LogicalProofType
  , grammarV1IntrinsicClaimApplication
  , grammarV1IntrinsicRelationProposition
  ) where

import qualified Data.Text as Text
import qualified Data.Text.Read as TextRead
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
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1GenericKind (..)
  , GrammarV1GenericRequirement (..)
  , GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RelationOperator (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1StructuralMode (..)
  , GrammarV1Type (..)
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

-- | Elaborate intrinsic primitive types without representation guessing. The
-- closed parser carrier retains the exact U/I prefix, and this bridge is the
-- semantic point that distinguishes unsigned from signed fixed-width integers.
-- Width zero and widths that cannot fit Core's Int carrier fail closed.
grammarV1PrimitiveType :: GrammarV1Type -> Maybe Ty
grammarV1PrimitiveType sourceType = case sourceType of
  GrammarV1UnitType -> Just TyUnit
  GrammarV1BoolType -> Just TyBool
  GrammarV1UnsignedType widthText ->
    case Text.uncons widthText of
      Just ('U', _) -> TyUInt <$> grammarV1IntegerWidth 'U' widthText
      Just ('I', _) -> TySInt <$> grammarV1IntegerWidth 'I' widthText
      _ -> Nothing
  _ -> Nothing

grammarV1IntegerWidth :: Char -> Text.Text -> Maybe Int
grammarV1IntegerWidth prefix widthText = do
  digits <- Text.stripPrefix (Text.singleton prefix) widthText
  case TextRead.decimal digits :: Either String (Integer, Text.Text) of
    Right (width, rest)
      | Text.null rest
      , width > 0
      , width <= toInteger (maxBound :: Int) -> Just (fromInteger width)
    _ -> Nothing

-- | Elaborate only scalar literal expressions whose Core reference-term meaning
-- is intrinsic and context-free. Integer literals become Nat terms and Boolean
-- literals remain Boolean terms. A negative decimal literal is intentionally not
-- a Nat; signed fixed-width interpretation is contextual and handled by the
-- signed runtime-scalar bridge.
grammarV1IntrinsicRefLiteral :: GrammarV1Expression -> Maybe RefTerm
grammarV1IntrinsicRefLiteral expression = case expression of
  GrammarV1IntegerExpression literalText ->
    RefNat <$> grammarV1NaturalLiteral literalText
  GrammarV1BoolExpression value -> Just (RefBool value)
  _ -> Nothing

grammarV1NaturalLiteral :: Text.Text -> Maybe Integer
grammarV1NaturalLiteral literalText =
  case TextRead.decimal literalText :: Either String (Integer, Text.Text) of
    Right (literal, rest)
      | Text.null rest -> Just literal
    _ -> Nothing

-- | Elaborate the context-free Bytes fragment only when its size expression has
-- already-established intrinsic Nat meaning. A Boolean literal, name, call,
-- projection, or compound expression remains outside this bridge; in particular
-- this function never invents a binding for a source name merely to form TyBytes.
grammarV1IntrinsicBytesType :: GrammarV1Type -> Maybe Ty
grammarV1IntrinsicBytesType sourceType = case sourceType of
  GrammarV1BytesType (Located _ sizeExpression) ->
    case grammarV1IntrinsicRefLiteral sizeExpression of
      Just size@(RefNat _) -> Just (TyBytes size)
      _ -> Nothing
  _ -> Nothing

-- | Preserve a Grammar-v1 Proof[...] type exactly when its proposition belongs
-- to the already-verified context-free logical fragment. Relation and claim
-- leaves remain unresolved for later contextual elaboration rather than being
-- invented or reinterpreted merely to construct TyProof.
grammarV1LogicalProofType :: GrammarV1Type -> Maybe Ty
grammarV1LogicalProofType sourceType = case sourceType of
  GrammarV1ProofType (Located _ proposition) ->
    TyProof <$> grammarV1LogicalProposition proposition
  _ -> Nothing

-- | Preserve a bare, unspecialized claim reference and intrinsic scalar literal
-- arguments exactly as one Core atom. This is syntactic identity plumbing only:
-- claim existence, arity, and argument sorts remain the competent semantic
-- checker's responsibility. Specialized claim references and contextual argument
-- expressions fail closed rather than acquiring invented bindings or static
-- instantiations.
grammarV1IntrinsicClaimApplication :: GrammarV1Proposition -> Maybe Proposition
grammarV1IntrinsicClaimApplication source = case source of
  GrammarV1ClaimApplicationProposition reference arguments
    | null (grammarV1StaticReferenceArguments reference) -> do
        claim <- case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts -> Just (Text.intercalate (Text.singleton '.') parts)
        terms <- mapM (grammarV1IntrinsicRefLiteral . locatedValue) arguments
        Just (Atom claim terms)
  _ -> Nothing

-- | Compose the already-verified relation-operator mapping with only the
-- context-free scalar literal reference terms established by #477. Contextual
-- names, arithmetic expressions, calls, projections, and other operands remain
-- unresolved so this bridge cannot invent a binding or term interpretation just
-- to make a relation elaborate.
grammarV1IntrinsicRelationProposition
  :: GrammarV1Proposition
  -> Maybe Proposition
grammarV1IntrinsicRelationProposition source = case source of
  GrammarV1RelationProposition
    (Located _ left)
    (Located _ operator)
    (Located _ right) ->
      grammarV1RelationProposition operator
        <$> grammarV1IntrinsicRefLiteral left
        <*> grammarV1IntrinsicRefLiteral right
  _ -> Nothing
