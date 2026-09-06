module Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewriteExpressionReferences
  , grammarV1RewritePropositionReferences
  , grammarV1RewriteTypeReferences
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Syntax (Name (..))
import Phil.Surface.Check.Support
  ( insertBindingMeta
  , shapeForBinding
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Fallback (..)
  , GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Insert one already-resolved Grammar-v1 binder into the legacy SurfaceState
-- under its generated semantic Core Name rather than its author-facing spelling.
-- The existing SurfaceState/BindingMeta machinery remains the resource/type
-- carrier, but its Text lookup key on this path is now internal semantic identity.
-- Record field aliases are rebased onto the same semantic name before insertion.
grammarV1InsertSemanticBinding
  :: GrammarV1ResolvedBinder
  -> BindingMeta
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
grammarV1InsertSemanticBinding binder meta state =
  insertBindingMeta
    (grammarV1ResolvedBinderSourceSpan binder)
    semanticText
    meta
      { bindingShape = shapeForBinding semanticText (bindingShape meta)
      }
    state
  where
    Name semanticText = grammarV1ResolvedBinderCoreName binder

-- | Rewrite exactly the term-name occurrences that LexicalReferenceScope has
-- already resolved to lexical binders. Unresolved/global/static names are left
-- untouched. Unsupported command expressions remain outside this bridge rather
-- than acquiring a second interpretation merely to reach the legacy checker.
grammarV1RewriteExpressionReferences
  :: [GrammarV1CheckedLexicalReference]
  -> Located GrammarV1Expression
  -> Maybe (Located GrammarV1Expression)
grammarV1RewriteExpressionReferences references = rewriteExpression renames
  where
    renames = referenceRenameMap references

-- | Apply the same exact-occurrence renaming to the bounded proposition fragment
-- already admitted by LexicalReferenceScope and BoundProposition.
grammarV1RewritePropositionReferences
  :: [GrammarV1CheckedLexicalReference]
  -> Located GrammarV1Proposition
  -> Maybe (Located GrammarV1Proposition)
grammarV1RewritePropositionReferences references = rewriteProposition renames
  where
    renames = referenceRenameMap references

-- | Apply exact lexical renaming inside the type fragment for which
-- ProtocolBinderScope already records dependency references. Refinement types are
-- deliberately left outside this bounded adapter because their local refinement
-- binder is a distinct dependent-type authority.
grammarV1RewriteTypeReferences
  :: [GrammarV1CheckedLexicalReference]
  -> Located GrammarV1Type
  -> Maybe (Located GrammarV1Type)
grammarV1RewriteTypeReferences references = rewriteType renames
  where
    renames = referenceRenameMap references

referenceRenameMap
  :: [GrammarV1CheckedLexicalReference]
  -> Map.Map (Located Text) Text
referenceRenameMap = Map.fromList . map entry
  where
    entry reference =
      ( grammarV1CheckedLexicalReferenceSource reference
      , semanticText (grammarV1CheckedLexicalReferenceBinder reference)
      )
    semanticText binder =
      case grammarV1ResolvedBinderCoreName binder of
        Name name -> name

rewriteExpression
  :: Map.Map (Located Text) Text
  -> Located GrammarV1Expression
  -> Maybe (Located GrammarV1Expression)
rewriteExpression renames (Located span' expression) =
  Located span' <$> case expression of
    GrammarV1NameExpression reference arguments -> do
      rewrittenArguments <- mapM (rewriteExpression renames) arguments
      let rewrittenReference
            | null arguments
            , null (grammarV1StaticReferenceArguments reference)
            , [displayName] <- grammarV1QualifiedNameParts
                (grammarV1StaticReferenceName reference)
            , Just semanticName <- Map.lookup (Located span' displayName) renames =
                reference
                  { grammarV1StaticReferenceName =
                      GrammarV1QualifiedName [semanticName]
                  }
            | otherwise = reference
      pure (GrammarV1NameExpression rewrittenReference rewrittenArguments)
    GrammarV1BoolExpression value -> pure (GrammarV1BoolExpression value)
    GrammarV1UnitExpression -> pure GrammarV1UnitExpression
    GrammarV1IntegerExpression value -> pure (GrammarV1IntegerExpression value)
    GrammarV1ProjectionExpression receiver field ->
      GrammarV1ProjectionExpression
        <$> rewriteExpression renames receiver
        <*> pure field
    GrammarV1ShiftExpression left operator right ->
      GrammarV1ShiftExpression
        <$> rewriteExpression renames left
        <*> pure operator
        <*> rewriteExpression renames right
    GrammarV1BinaryExpression left operator right ->
      GrammarV1BinaryExpression
        <$> rewriteExpression renames left
        <*> pure operator
        <*> rewriteExpression renames right
    GrammarV1FallbackExpression primary fallback ->
      GrammarV1FallbackExpression
        <$> rewriteExpression renames primary
        <*> rewriteFallback renames fallback
    GrammarV1ConvertExpression value target ->
      GrammarV1ConvertExpression
        <$> rewriteExpression renames value
        <*> pure target
    GrammarV1TupleExpression elements ->
      GrammarV1TupleExpression <$> mapM (rewriteExpression renames) elements
    GrammarV1ParenthesizedExpression inner ->
      GrammarV1ParenthesizedExpression <$> rewriteExpression renames inner
    _ -> Nothing

rewriteFallback
  :: Map.Map (Located Text) Text
  -> Located GrammarV1Fallback
  -> Maybe (Located GrammarV1Fallback)
rewriteFallback renames (Located span' fallback) =
  Located span' <$> case fallback of
    GrammarV1FailFallback target ->
      GrammarV1FailFallback <$> rewriteFailureTarget renames target
    GrammarV1RejectFallback expression ->
      GrammarV1RejectFallback <$> rewriteExpression renames expression

rewriteFailureTarget
  :: Map.Map (Located Text) Text
  -> Located GrammarV1FailureTarget
  -> Maybe (Located GrammarV1FailureTarget)
rewriteFailureTarget renames (Located span' target) = do
  arguments <- mapM
    (rewriteExpression renames)
    (grammarV1FailureTargetArguments target)
  pure (Located span' target { grammarV1FailureTargetArguments = arguments })

rewriteProposition
  :: Map.Map (Located Text) Text
  -> Located GrammarV1Proposition
  -> Maybe (Located GrammarV1Proposition)
rewriteProposition renames (Located span' proposition) =
  Located span' <$> case proposition of
    GrammarV1TrueProposition -> pure GrammarV1TrueProposition
    GrammarV1FalseProposition -> pure GrammarV1FalseProposition
    GrammarV1RelationProposition left operator right ->
      GrammarV1RelationProposition
        <$> rewriteExpression renames left
        <*> pure operator
        <*> rewriteExpression renames right
    GrammarV1ClaimApplicationProposition reference arguments ->
      GrammarV1ClaimApplicationProposition reference
        <$> mapM (rewriteExpression renames) arguments
    GrammarV1NotProposition inner ->
      GrammarV1NotProposition <$> rewriteProposition renames inner
    GrammarV1AndProposition left right ->
      GrammarV1AndProposition
        <$> rewriteProposition renames left
        <*> rewriteProposition renames right
    GrammarV1OrProposition left right ->
      GrammarV1OrProposition
        <$> rewriteProposition renames left
        <*> rewriteProposition renames right

rewriteType
  :: Map.Map (Located Text) Text
  -> Located GrammarV1Type
  -> Maybe (Located GrammarV1Type)
rewriteType renames (Located span' ty) =
  Located span' <$> case ty of
    GrammarV1UnitType -> pure GrammarV1UnitType
    GrammarV1BoolType -> pure GrammarV1BoolType
    GrammarV1UnsignedType width -> pure (GrammarV1UnsignedType width)
    GrammarV1BytesType expression ->
      GrammarV1BytesType <$> rewriteExpression renames expression
    GrammarV1FrameType reference -> pure (GrammarV1FrameType reference)
    GrammarV1ProofType proposition ->
      GrammarV1ProofType <$> rewriteProposition renames proposition
    GrammarV1ValidatedType claim context subject ->
      GrammarV1ValidatedType claim
        <$> rewriteExpression renames context
        <*> rewriteExpression renames subject
    GrammarV1RefinementType _ _ _ -> Nothing
    GrammarV1TupleType elements ->
      GrammarV1TupleType <$> mapM (rewriteType renames) elements
    GrammarV1NamedType reference -> pure (GrammarV1NamedType reference)
