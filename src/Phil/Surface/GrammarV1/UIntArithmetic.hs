module Phil.Surface.GrammarV1.UIntArithmetic
  ( GrammarV1UIntEnvironment
  , GrammarV1PlainUIntArithmeticError (..)
  , checkGrammarV1PlainUIntArithmetic
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState
  , CheckerError
  , emitObligation
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Syntax
  ( RefTerm (..)
  , Ty (..)
  )
import Phil.Core.UIntArithmetic
  ( PlainUIntArithmeticDecision (..)
  , PlainUIntArithmeticSite
  , UIntArithmeticError
  , UIntArithmeticOperator (..)
  , checkPlainUIntArithmetic
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
  , grammarV1ContextualUIntLiteral
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact already-resolved semantic leaves available to one Grammar-v1
-- arithmetic expression.  The key retains the complete static-reference shape;
-- this bridge never resolves by display spelling alone.
type GrammarV1UIntEnvironment = Map GrammarV1StaticReference RefTerm

-- | Fail-closed errors for the bounded EXEC-008 Grammar-v1 composition.
data GrammarV1PlainUIntArithmeticError
  = GrammarV1PlainUIntContextRequired GrammarV1Type
  | GrammarV1PlainUIntBinaryExpressionRequired GrammarV1Expression
  | GrammarV1PlainUIntOperatorNotPlainArithmetic GrammarV1BinaryOperator
  | GrammarV1PlainUIntUnsupportedOperand GrammarV1Expression
  | GrammarV1PlainUIntUnknownReference GrammarV1StaticReference
  | GrammarV1PlainUIntLiteralError GrammarV1RuntimeScalarError
  | GrammarV1PlainUIntLiteralIdentityMismatch ScalarLiteral
  | GrammarV1PlainUIntCoreError UIntArithmeticError
  | GrammarV1PlainUIntObligationError CheckerError
  deriving (Eq, Show)

-- | Compose one canonical Grammar-v1 plain UInt '+', '-', or '*' expression
-- with the Core EXEC-008 arithmetic judgment. Division and remainder are owned
-- by the separate EXEC-017 integer-division bridge and cannot be reinterpreted
-- here as multiplication or another already-supported arithmetic operation.
checkGrammarV1PlainUIntArithmetic
  :: CheckState
  -> GrammarV1Type
  -> GrammarV1UIntEnvironment
  -> GrammarV1Expression
  -> RefTerm
  -> PlainUIntArithmeticSite
  -> Either
      GrammarV1PlainUIntArithmeticError
      (PlainUIntArithmeticDecision, CheckState)
checkGrammarV1PlainUIntArithmetic state contextualType environment expression result site = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TyUInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1PlainUIntContextRequired contextualType)
  (leftExpression, operator, rightExpression) <- case expression of
    GrammarV1BinaryExpression left locatedOperator right ->
      Right (locatedValue left, locatedValue locatedOperator, locatedValue right)
    _ -> Left (GrammarV1PlainUIntBinaryExpressionRequired expression)
  left <- resolveOperand contextualType environment leftExpression
  right <- resolveOperand contextualType environment rightExpression
  coreOperator <- case operator of
    GrammarV1Add -> Right UIntAdd
    GrammarV1Subtract -> Right UIntSubtract
    GrammarV1Multiply -> Right UIntMultiply
    GrammarV1Divide -> Left (GrammarV1PlainUIntOperatorNotPlainArithmetic operator)
    GrammarV1Remainder -> Left (GrammarV1PlainUIntOperatorNotPlainArithmetic operator)
  decision <- mapLeft GrammarV1PlainUIntCoreError
    (checkPlainUIntArithmetic state coreOperator width left right result site)
  nextState <- case decision of
    PlainUIntArithmeticEstablished _ -> Right state
    PlainUIntArithmeticRequiresProof obligation ->
      mapLeft GrammarV1PlainUIntObligationError (emitObligation obligation state)
  Right (decision, nextState)

resolveOperand
  :: GrammarV1Type
  -> GrammarV1UIntEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1PlainUIntArithmeticError RefTerm
resolveOperand contextualType environment expression =
  case expression of
    GrammarV1IntegerExpression _ -> do
      literal <- mapLeft GrammarV1PlainUIntLiteralError
        (grammarV1ContextualUIntLiteral contextualType expression)
      case literal of
        ScalarUIntLiteral width value -> Right (RefUInt width value)
        _ -> Left (GrammarV1PlainUIntLiteralIdentityMismatch literal)
    GrammarV1NameExpression reference arguments
      | null arguments ->
          case Map.lookup reference environment of
            Just term -> Right term
            Nothing -> Left (GrammarV1PlainUIntUnknownReference reference)
      | otherwise -> Left (GrammarV1PlainUIntUnsupportedOperand expression)
    _ -> Left (GrammarV1PlainUIntUnsupportedOperand expression)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
