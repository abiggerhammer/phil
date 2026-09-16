module Phil.Surface.GrammarV1.FloatArithmetic
  ( GrammarV1FloatEnvironment
  , GrammarV1FloatArithmeticError (..)
  , evaluateGrammarV1FloatExpression
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.FloatArithmetic
  ( FloatFormat
  , FloatOperator (..)
  , FloatSemanticError
  , FloatValue
  , applyFloatOperator
  , floatFormat
  , floatTypeFromCoreType
  , negateFloatValue
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Expression (..)
  , GrammarV1StaticReference
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError
  , grammarV1ContextualFloatLiteral
  )
import Phil.Surface.Syntax (Located (..))

type GrammarV1FloatEnvironment = Map GrammarV1StaticReference FloatValue

data GrammarV1FloatArithmeticError
  = GrammarV1FloatContextRequired GrammarV1Type
  | GrammarV1FloatUnsupportedOperator GrammarV1BinaryOperator
  | GrammarV1FloatUnsupportedOperand GrammarV1Expression
  | GrammarV1FloatUnknownReference GrammarV1StaticReference
  | GrammarV1FloatOperandFormatMismatch FloatFormat FloatFormat
  | GrammarV1FloatLiteralError GrammarV1RuntimeScalarError
  | GrammarV1FloatCoreError FloatSemanticError
  deriving (Eq, Show)

-- | Evaluate one Grammar-v1 floating expression against the exact EXEC-018
-- semantic authority. The environment contains semantic FloatValues, not host
-- Float/Double values, so parsed arithmetic never delegates its meaning to the
-- implementation language or target backend.
evaluateGrammarV1FloatExpression
  :: GrammarV1Type
  -> GrammarV1FloatEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1FloatArithmeticError FloatValue
evaluateGrammarV1FloatExpression contextualType environment expression = do
  format <- case grammarV1PrimitiveType contextualType >>= floatTypeFromCoreType of
    Just exactFormat -> Right exactFormat
    Nothing -> Left (GrammarV1FloatContextRequired contextualType)
  evaluate format expression
  where
    evaluate format source = case source of
      GrammarV1IntegerExpression _ ->
        mapLeft GrammarV1FloatLiteralError
          (grammarV1ContextualFloatLiteral contextualType source)
      GrammarV1NameExpression reference arguments
        | null arguments -> do
            value <- case Map.lookup reference environment of
              Just exactValue -> Right exactValue
              Nothing -> Left (GrammarV1FloatUnknownReference reference)
            if floatFormat value == format
              then Right value
              else Left
                (GrammarV1FloatOperandFormatMismatch format (floatFormat value))
        | otherwise -> Left (GrammarV1FloatUnsupportedOperand source)
      GrammarV1NegateExpression (Located _ inner) ->
        negateFloatValue <$> evaluate format inner
      GrammarV1BinaryExpression left locatedOperator right -> do
        operator <- case locatedValue locatedOperator of
          GrammarV1Add -> Right FloatAdd
          GrammarV1Subtract -> Right FloatSubtract
          GrammarV1Multiply -> Right FloatMultiply
          GrammarV1Divide -> Right FloatDivide
          GrammarV1Remainder ->
            Left (GrammarV1FloatUnsupportedOperator GrammarV1Remainder)
        leftValue <- evaluate format (locatedValue left)
        rightValue <- evaluate format (locatedValue right)
        mapLeft GrammarV1FloatCoreError
          (applyFloatOperator operator leftValue rightValue)
      GrammarV1ParenthesizedExpression (Located _ inner) -> evaluate format inner
      _ -> Left (GrammarV1FloatUnsupportedOperand source)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
