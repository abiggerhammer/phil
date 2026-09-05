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
  , checkPlainSIntArithmetic
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Syntax
  ( RefTerm (..)
  , Ty (..)
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
  , grammarV1ContextualSIntLiteral
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact already-resolved semantic leaves available to one signed arithmetic
-- expression. Static-reference identity is preserved exactly; signedness is not
-- inferred from spelling at this stage.
type GrammarV1SIntEnvironment = Map GrammarV1StaticReference RefTerm

data GrammarV1PlainSIntArithmeticError
  = GrammarV1PlainSIntContextRequired GrammarV1Type
  | GrammarV1PlainSIntBinaryExpressionRequired GrammarV1Expression
  | GrammarV1PlainSIntUnsupportedOperand GrammarV1Expression
  | GrammarV1PlainSIntUnknownReference GrammarV1StaticReference
  | GrammarV1PlainSIntLiteralError GrammarV1RuntimeScalarError
  | GrammarV1PlainSIntLiteralIdentityMismatch ScalarLiteral
  | GrammarV1PlainSIntCoreError SIntArithmeticError
  | GrammarV1PlainSIntObligationError CheckerError
  deriving (Eq, Show)

-- | Compose one canonical Grammar-v1 I[w] '+', '-', or '*' expression with the
-- exact Core signed arithmetic judgment. Closed operations are mathematical and
-- must remain in range; symbolic operations emit the ordinary residual proof
-- obligation. No target wrap, saturation, trap, poison, or signed-overflow UB is
-- selected by this bridge.
checkGrammarV1PlainSIntArithmetic
  :: CheckState
  -> GrammarV1Type
  -> GrammarV1SIntEnvironment
  -> GrammarV1Expression
  -> RefTerm
  -> PlainSIntArithmeticSite
  -> Either
      GrammarV1PlainSIntArithmeticError
      (PlainSIntArithmeticDecision, CheckState)
checkGrammarV1PlainSIntArithmetic state contextualType environment expression result site = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TySInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1PlainSIntContextRequired contextualType)
  (leftExpression, operator, rightExpression) <- case expression of
    GrammarV1BinaryExpression left locatedOperator right ->
      Right (locatedValue left, locatedValue locatedOperator, locatedValue right)
    _ -> Left (GrammarV1PlainSIntBinaryExpressionRequired expression)
  left <- resolveOperand contextualType environment leftExpression
  right <- resolveOperand contextualType environment rightExpression
  let coreOperator = case operator of
        GrammarV1Add -> SIntAdd
        GrammarV1Subtract -> SIntSubtract
        GrammarV1Multiply -> SIntMultiply
  decision <- mapLeft GrammarV1PlainSIntCoreError
    (checkPlainSIntArithmetic state coreOperator width left right result site)
  nextState <- case decision of
    PlainSIntArithmeticEstablished _ -> Right state
    PlainSIntArithmeticRequiresProof obligation ->
      mapLeft GrammarV1PlainSIntObligationError (emitObligation obligation state)
  Right (decision, nextState)

resolveOperand
  :: GrammarV1Type
  -> GrammarV1SIntEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1PlainSIntArithmeticError RefTerm
resolveOperand contextualType environment expression =
  case expression of
    GrammarV1IntegerExpression _ -> do
      literal <- mapLeft GrammarV1PlainSIntLiteralError
        (grammarV1ContextualSIntLiteral contextualType expression)
      case literal of
        ScalarSIntLiteral width value -> Right (RefSInt width value)
        _ -> Left (GrammarV1PlainSIntLiteralIdentityMismatch literal)
    GrammarV1NameExpression reference arguments
      | null arguments ->
          case Map.lookup reference environment of
            Just term -> Right term
            Nothing -> Left (GrammarV1PlainSIntUnknownReference reference)
      | otherwise -> Left (GrammarV1PlainSIntUnsupportedOperand expression)
    _ -> Left (GrammarV1PlainSIntUnsupportedOperand expression)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
