module Phil.Surface.GrammarV1.SIntArithmetic
  ( GrammarV1SIntEnvironment
  , GrammarV1PlainSIntArithmeticError (..)
  , checkGrammarV1PlainSIntArithmetic
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState
  , CheckerError
  , emitObligation
  )
import Phil.Core.SIntArithmetic
  ( PlainSIntArithmeticDecision (..)
  , PlainSIntArithmeticSite
  , SIntArithmeticError
  , SIntArithmeticOperator (..)
  , SIntLiteral (..)
  , SIntTerm (..)
  , sIntLiteralInRange
  , checkPlainSIntArithmetic
  , sIntTypeFromCoreType
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Expression (..)
  , GrammarV1StaticReference
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.RuntimeScalar
  ( GrammarV1RuntimeScalarError (..)
  , grammarV1ContextualSIntLiteral
  )
import Phil.Surface.Syntax (Located (..))

type GrammarV1SIntEnvironment = Map GrammarV1StaticReference SIntTerm

data GrammarV1PlainSIntArithmeticError
  = GrammarV1PlainSIntContextRequired GrammarV1Type
  | GrammarV1PlainSIntBinaryExpressionRequired GrammarV1Expression
  | GrammarV1PlainSIntOperatorNotPlainArithmetic GrammarV1BinaryOperator
  | GrammarV1PlainSIntUnsupportedOperand GrammarV1Expression
  | GrammarV1PlainSIntUnknownReference GrammarV1StaticReference
  | GrammarV1PlainSIntLiteralError GrammarV1RuntimeScalarError
  | GrammarV1PlainSIntNegationOutOfRange SIntLiteral
  | GrammarV1PlainSIntCoreError SIntArithmeticError
  | GrammarV1PlainSIntObligationError CheckerError
  deriving (Eq, Show)

checkGrammarV1PlainSIntArithmetic
  :: CheckState
  -> GrammarV1Type
  -> GrammarV1SIntEnvironment
  -> GrammarV1Expression
  -> SIntTerm
  -> PlainSIntArithmeticSite
  -> Either
      GrammarV1PlainSIntArithmeticError
      (PlainSIntArithmeticDecision, CheckState)
checkGrammarV1PlainSIntArithmetic state contextualType environment expression result site = do
  ty <- case grammarV1PrimitiveType contextualType >>= sIntTypeFromCoreType of
    Just exactType -> Right exactType
    Nothing -> Left (GrammarV1PlainSIntContextRequired contextualType)
  (leftExpression, operator, rightExpression) <- case expression of
    GrammarV1BinaryExpression left locatedOperator right ->
      Right (locatedValue left, locatedValue locatedOperator, locatedValue right)
    _ -> Left (GrammarV1PlainSIntBinaryExpressionRequired expression)
  left <- resolveOperand contextualType environment leftExpression
  right <- resolveOperand contextualType environment rightExpression
  coreOperator <- case operator of
    GrammarV1Add -> Right SIntAdd
    GrammarV1Subtract -> Right SIntSubtract
    GrammarV1Multiply -> Right SIntMultiply
    GrammarV1Divide -> Left (GrammarV1PlainSIntOperatorNotPlainArithmetic operator)
    GrammarV1Remainder -> Left (GrammarV1PlainSIntOperatorNotPlainArithmetic operator)
  decision <- mapLeft GrammarV1PlainSIntCoreError
    (checkPlainSIntArithmetic state coreOperator ty left right result site)
  nextState <- case decision of
    PlainSIntArithmeticEstablished _ -> Right state
    PlainSIntArithmeticRequiresProof obligation ->
      mapLeft GrammarV1PlainSIntObligationError (emitObligation obligation state)
  Right (decision, nextState)

resolveOperand
  :: GrammarV1Type
  -> GrammarV1SIntEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1PlainSIntArithmeticError SIntTerm
resolveOperand contextualType environment expression =
  case expression of
    GrammarV1IntegerExpression _ ->
      SIntKnown <$> mapLeft GrammarV1PlainSIntLiteralError
        (grammarV1ContextualSIntLiteral contextualType expression)
    GrammarV1NameExpression reference arguments
      | null arguments ->
          case Map.lookup reference environment of
            Just term -> Right term
            Nothing -> Left (GrammarV1PlainSIntUnknownReference reference)
      | otherwise -> Left (GrammarV1PlainSIntUnsupportedOperand expression)
    GrammarV1NegateExpression operand ->
      case grammarV1ContextualSIntLiteral contextualType expression of
        Right literal -> Right (SIntKnown literal)
        Left (GrammarV1RuntimeIntegerLiteralRequired _) -> do
          term <- resolveOperand contextualType environment (locatedValue operand)
          case term of
            SIntKnown literal ->
              let negated = SIntLiteral
                    (sIntLiteralType literal)
                    (negate (sIntLiteralValue literal))
              in if sIntLiteralInRange negated
                  then Right (SIntKnown negated)
                  else Left (GrammarV1PlainSIntNegationOutOfRange negated)
            SIntSymbolic {} -> Left (GrammarV1PlainSIntUnsupportedOperand expression)
        Left err -> Left (GrammarV1PlainSIntLiteralError err)
    GrammarV1ParenthesizedExpression (Located _ inner) ->
      resolveOperand contextualType environment inner
    _ -> Left (GrammarV1PlainSIntUnsupportedOperand expression)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
