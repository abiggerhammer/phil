module Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  , GrammarV1LexicalReferenceError (..)
  , grammarV1CheckedExpressionReferences
  , grammarV1CheckedPropositionReferences
  , grammarV1CheckedTypeReferences
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1ResolveLocal
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1Fallback (..)
  , GrammarV1FailureTarget (..)
  , GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | One term-level source occurrence that resolves to an already-active lexical
-- binder. Static/global names are deliberately ignored when they do not collide
-- with a caller-supplied set of not-yet-visible lexical names.
data GrammarV1CheckedLexicalReference = GrammarV1CheckedLexicalReference
  { grammarV1CheckedLexicalReferenceSource :: Located Text
  , grammarV1CheckedLexicalReferenceBinder :: GrammarV1ResolvedBinder
  }
  deriving (Eq, Show)

data GrammarV1LexicalReferenceError
  = GrammarV1LexicalReferenceBinderError GrammarV1BinderScopeError
  | GrammarV1LexicalReferenceForwardReference (Located Text)
  deriving (Eq, Show)

-- | Resolve lexical references in the bounded Grammar-v1 expression fragment
-- shared by join/loop telescope dependencies. Unsupported command expressions
-- fail closed by returning Nothing instead of guessing their scope behavior.
grammarV1CheckedExpressionReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either GrammarV1LexicalReferenceError [GrammarV1CheckedLexicalReference])
grammarV1CheckedExpressionReferences pending scope (Located sourceSpan expression) =
  case expression of
    GrammarV1NameExpression reference arguments
      | null arguments
      , null (grammarV1StaticReferenceArguments reference)
      , [displayName] <- grammarV1QualifiedNameParts
          (grammarV1StaticReferenceName reference) ->
          let sourceName = Located sourceSpan displayName
          in case grammarV1ResolveLocal sourceName scope of
              Right binder -> Just (Right
                [GrammarV1CheckedLexicalReference sourceName binder])
              Left (GrammarV1BinderNotInScope _)
                | Set.member displayName pending ->
                    Just (Left
                      (GrammarV1LexicalReferenceForwardReference sourceName))
                | otherwise -> Just (Right [])
              Left scopeError -> Just (Left
                (GrammarV1LexicalReferenceBinderError scopeError))
    GrammarV1NameExpression _ arguments -> checkedMany
      (map (grammarV1CheckedExpressionReferences pending scope) arguments)
    GrammarV1BoolExpression _ -> Just (Right [])
    GrammarV1UnitExpression -> Just (Right [])
    GrammarV1IntegerExpression _ -> Just (Right [])
    GrammarV1ProjectionExpression receiver _ ->
      grammarV1CheckedExpressionReferences pending scope receiver
    GrammarV1BinaryExpression left _ right -> combineChecked
      (grammarV1CheckedExpressionReferences pending scope left)
      (grammarV1CheckedExpressionReferences pending scope right)
    GrammarV1FallbackExpression primary fallback -> combineChecked
      (grammarV1CheckedExpressionReferences pending scope primary)
      (checkedFallbackReferences pending scope fallback)
    GrammarV1ConvertExpression value _ ->
      grammarV1CheckedExpressionReferences pending scope value
    GrammarV1TupleExpression elements -> checkedMany
      (map (grammarV1CheckedExpressionReferences pending scope) elements)
    GrammarV1ParenthesizedExpression inner ->
      grammarV1CheckedExpressionReferences pending scope inner
    _ -> Nothing

grammarV1CheckedPropositionReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Proposition
  -> Maybe
      (Either GrammarV1LexicalReferenceError [GrammarV1CheckedLexicalReference])
grammarV1CheckedPropositionReferences pending scope (Located _ proposition) =
  case proposition of
    GrammarV1TrueProposition -> Just (Right [])
    GrammarV1FalseProposition -> Just (Right [])
    GrammarV1RelationProposition left _ right -> combineChecked
      (grammarV1CheckedExpressionReferences pending scope left)
      (grammarV1CheckedExpressionReferences pending scope right)
    GrammarV1ClaimApplicationProposition _ arguments -> checkedMany
      (map (grammarV1CheckedExpressionReferences pending scope) arguments)
    GrammarV1NotProposition inner ->
      grammarV1CheckedPropositionReferences pending scope inner
    GrammarV1AndProposition left right -> combineChecked
      (grammarV1CheckedPropositionReferences pending scope left)
      (grammarV1CheckedPropositionReferences pending scope right)
    GrammarV1OrProposition left right -> combineChecked
      (grammarV1CheckedPropositionReferences pending scope left)
      (grammarV1CheckedPropositionReferences pending scope right)

grammarV1CheckedTypeReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Type
  -> Maybe
      (Either GrammarV1LexicalReferenceError [GrammarV1CheckedLexicalReference])
grammarV1CheckedTypeReferences pending scope (Located _ ty) = case ty of
  GrammarV1UnitType -> Just (Right [])
  GrammarV1BoolType -> Just (Right [])
  GrammarV1UnsignedType _ -> Just (Right [])
  GrammarV1BytesType expression ->
    grammarV1CheckedExpressionReferences pending scope expression
  GrammarV1FrameType _ -> Just (Right [])
  GrammarV1ProofType proposition ->
    grammarV1CheckedPropositionReferences pending scope proposition
  GrammarV1ValidatedType _ context subject -> combineChecked
    (grammarV1CheckedExpressionReferences pending scope context)
    (grammarV1CheckedExpressionReferences pending scope subject)
  GrammarV1RefinementType _ _ _ -> Nothing
  GrammarV1TupleType elements -> checkedMany
    (map (grammarV1CheckedTypeReferences pending scope) elements)
  GrammarV1NamedType _ -> Just (Right [])

checkedFallbackReferences
  :: Set.Set Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Fallback
  -> Maybe
      (Either GrammarV1LexicalReferenceError [GrammarV1CheckedLexicalReference])
checkedFallbackReferences pending scope (Located _ fallback) = case fallback of
  GrammarV1FailFallback (Located _ target) -> checkedMany
    (map (grammarV1CheckedExpressionReferences pending scope)
      (grammarV1FailureTargetArguments target))
  GrammarV1RejectFallback expression ->
    grammarV1CheckedExpressionReferences pending scope expression

combineChecked
  :: Maybe (Either e [a])
  -> Maybe (Either e [a])
  -> Maybe (Either e [a])
combineChecked left right = do
  leftResult <- left
  rightResult <- right
  Just $ do
    leftValues <- leftResult
    rightValues <- rightResult
    Right (leftValues <> rightValues)

checkedMany :: [Maybe (Either e [a])] -> Maybe (Either e [a])
checkedMany = foldr combineChecked (Just (Right []))
