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
import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , floatCoreType
  )
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence
  , competenceForRequirementCategory
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Core.SIntArithmetic (SIntType (..), sIntCoreType)
import Phil.Core.UnicodeChar (unicodeCharCoreType)
import Phil.Core.UnicodeString (unicodeStringCoreType)
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

grammarV1GenericRequirementCompetence
  :: GrammarV1GenericRequirement
  -> GenericRequirementCompetence
grammarV1GenericRequirementCompetence =
  competenceForRequirementCategory . grammarV1GenericRequirementCategory

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

grammarV1StructuralMode :: GrammarV1StructuralMode -> Mode
grammarV1StructuralMode sourceMode = case sourceMode of
  GrammarV1Unrestricted -> Unrestricted
  GrammarV1Affine -> Affine
  GrammarV1Linear -> Linear

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

-- | The closed parser carrier preserves exact primitive spelling. U[w] keeps
-- its existing Core constructor; I[w] and F32/F64 receive exact semantic type
-- identities owned by their dedicated scalar authorities without widening the
-- Phase-0 backend ScalarType carrier. Char and String share this closed primitive
-- spelling carrier while denoting semantic Unicode values rather than encodings.
grammarV1PrimitiveType :: GrammarV1Type -> Maybe Ty
grammarV1PrimitiveType sourceType = case sourceType of
  GrammarV1UnitType -> Just TyUnit
  GrammarV1BoolType -> Just TyBool
  GrammarV1UnsignedType widthText
    | widthText == Text.pack "Char" -> Just unicodeCharCoreType
    | widthText == Text.pack "String" -> Just unicodeStringCoreType
    | widthText == Text.pack "F32" -> Just (floatCoreType Float32)
    | widthText == Text.pack "F64" -> Just (floatCoreType Float64)
    | otherwise ->
        case Text.uncons widthText of
          Just ('U', _) -> TyUInt <$> grammarV1IntegerWidth 'U' widthText
          Just ('I', _) -> sIntCoreType . SIntType <$> grammarV1IntegerWidth 'I' widthText
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

grammarV1IntrinsicBytesType :: GrammarV1Type -> Maybe Ty
grammarV1IntrinsicBytesType sourceType = case sourceType of
  GrammarV1BytesType (Located _ sizeExpression) ->
    case grammarV1IntrinsicRefLiteral sizeExpression of
      Just size@(RefNat _) -> Just (TyBytes size)
      _ -> Nothing
  _ -> Nothing

grammarV1LogicalProofType :: GrammarV1Type -> Maybe Ty
grammarV1LogicalProofType sourceType = case sourceType of
  GrammarV1ProofType (Located _ proposition) ->
    TyProof <$> grammarV1LogicalProposition proposition
  _ -> Nothing

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
