{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  ) where

import Phil.Core.Syntax (RefTerm (..))
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundRef (grammarV1BoundRefTerm)
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicRefLiteral)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Compose the already-verified intrinsic literal and live simple-reference
-- leaves into the structural Phase-1 refinement-expression fragment. This bridge
-- performs only syntax-to-Core plumbing: `len`, explicit `toNat`, Nat add/sub,
-- and literal scaling map to their designated RefTerm constructors. Sort and
-- coercion competence remains with Core focusing when a consumer supplies an
-- expected sort; projection remains unresolved until its declared result sort is
-- available. Unknown names, specialized/called non-intrinsics, division,
-- remainder, and symbolic-by-symbolic multiplication therefore fail closed.
grammarV1BoundRefExpression
  :: SurfaceState
  -> Located GrammarV1Expression
  -> Maybe RefTerm
grammarV1BoundRefExpression state located@(Located _ expression) =
  grammarV1IntrinsicRefLiteral expression
    <|> grammarV1BoundRefTerm state located
    <|> compound expression
  where
    compound source = case source of
      GrammarV1ParenthesizedExpression inner ->
        grammarV1BoundRefExpression state inner
      GrammarV1NameExpression reference arguments
        | null (grammarV1StaticReferenceArguments reference) ->
            case (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference), arguments) of
              (["len"], [value]) ->
                RefLen <$> grammarV1BoundRefExpression state value
              (["toNat"], [value]) ->
                RefToNat <$> grammarV1BoundRefExpression state value
              _ -> Nothing
      GrammarV1BinaryExpression left operator right ->
        case locatedValue operator of
          GrammarV1Add ->
            RefAdd
              <$> grammarV1BoundRefExpression state left
              <*> grammarV1BoundRefExpression state right
          GrammarV1Subtract ->
            RefSub
              <$> grammarV1BoundRefExpression state left
              <*> grammarV1BoundRefExpression state right
          GrammarV1Multiply -> scale left right
          GrammarV1Divide -> Nothing
          GrammarV1Remainder -> Nothing
      _ -> Nothing

    scale left right =
      case (naturalCoefficient left, naturalCoefficient right) of
        (Just coefficient, _) ->
          RefScale coefficient <$> grammarV1BoundRefExpression state right
        (_, Just coefficient) ->
          RefScale coefficient <$> grammarV1BoundRefExpression state left
        _ -> Nothing

    naturalCoefficient source =
      case grammarV1IntrinsicRefLiteral (locatedValue source) of
        Just (RefNat coefficient) -> Just coefficient
        _ -> Nothing

infixr 3 <|>
(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> right = right
left <|> _ = left
