module Phil.Surface.GrammarV1.IntegerDivision
  ( GrammarV1UIntDivisionEnvironment
  , GrammarV1SIntDivisionEnvironment
  , GrammarV1PlainUIntDivisionError (..)
  , GrammarV1PlainSIntDivisionError (..)
  , GrammarV1CheckedDivisionSourceError (..)
  , checkGrammarV1PlainUIntDivision
  , checkGrammarV1PlainSIntDivision
  , checkGrammarV1CheckedUIntDivision
  , checkGrammarV1CheckedSIntDivision
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState
  , CheckerError
  , emitObligation
  )
import Phil.Core.IntegerDivision
  ( CheckedDivisionResult
  , CheckedSIntDivisionError
  , CheckedUIntDivisionError
  , IntegerDivisionOperator (..)
  , PlainIntegerDivisionSite
  , PlainSIntDivisionDecision (..)
  , PlainUIntDivisionDecision (..)
  , SIntDivisionError
  , UIntDivisionError
  , checkCheckedSIntDivision
  , checkCheckedUIntDivision
  , checkPlainSIntDivision
  , checkPlainUIntDivision
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.SIntArithmetic
  ( SIntLiteral
  , SIntTerm (..)
  , sIntTypeFromCoreType
  )
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
  , grammarV1ContextualUIntLiteral
  )
import Phil.Surface.Syntax (Located (..))

type GrammarV1UIntDivisionEnvironment = Map GrammarV1StaticReference RefTerm

type GrammarV1SIntDivisionEnvironment = Map GrammarV1StaticReference SIntTerm

data GrammarV1PlainUIntDivisionError
  = GrammarV1PlainUIntDivisionContextRequired GrammarV1Type
  | GrammarV1PlainUIntDivisionExpressionRequired GrammarV1Expression
  | GrammarV1PlainUIntDivisionOperatorRequired GrammarV1BinaryOperator
  | GrammarV1PlainUIntDivisionUnsupportedOperand GrammarV1Expression
  | GrammarV1PlainUIntDivisionUnknownReference GrammarV1StaticReference
  | GrammarV1PlainUIntDivisionLiteralError GrammarV1RuntimeScalarError
  | GrammarV1PlainUIntDivisionLiteralIdentityMismatch ScalarLiteral
  | GrammarV1PlainUIntDivisionCoreError UIntDivisionError
  | GrammarV1PlainUIntDivisionObligationError CheckerError
  deriving (Eq, Show)

data GrammarV1PlainSIntDivisionError
  = GrammarV1PlainSIntDivisionContextRequired GrammarV1Type
  | GrammarV1PlainSIntDivisionExpressionRequired GrammarV1Expression
  | GrammarV1PlainSIntDivisionOperatorRequired GrammarV1BinaryOperator
  | GrammarV1PlainSIntDivisionUnsupportedOperand GrammarV1Expression
  | GrammarV1PlainSIntDivisionUnknownReference GrammarV1StaticReference
  | GrammarV1PlainSIntDivisionLiteralError GrammarV1RuntimeScalarError
  | GrammarV1PlainSIntDivisionCoreError SIntDivisionError
  | GrammarV1PlainSIntDivisionObligationError CheckerError
  deriving (Eq, Show)

data GrammarV1CheckedDivisionSourceError
  = GrammarV1CheckedDivisionExpressionRequired GrammarV1Expression
  | GrammarV1CheckedDivisionOperatorRequired GrammarV1BinaryOperator
  | GrammarV1CheckedUIntDivisionContextRequired GrammarV1Type
  | GrammarV1CheckedSIntDivisionContextRequired GrammarV1Type
  | GrammarV1CheckedUIntDivisionCoreError CheckedUIntDivisionError
  | GrammarV1CheckedSIntDivisionCoreError CheckedSIntDivisionError
  deriving (Eq, Show)

checkGrammarV1PlainUIntDivision
  :: CheckState
  -> GrammarV1Type
  -> GrammarV1UIntDivisionEnvironment
  -> GrammarV1Expression
  -> RefTerm
  -> PlainIntegerDivisionSite
  -> Either
      GrammarV1PlainUIntDivisionError
      (PlainUIntDivisionDecision, CheckState)
checkGrammarV1PlainUIntDivision state contextualType environment expression result site = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TyUInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1PlainUIntDivisionContextRequired contextualType)
  (leftExpression, operator, rightExpression) <-
    mapLeft GrammarV1PlainUIntDivisionExpressionRequired
      (binaryParts expression)
  coreOperator <- mapLeft GrammarV1PlainUIntDivisionOperatorRequired
    (integerDivisionOperator operator)
  left <- resolveUIntOperand contextualType environment leftExpression
  right <- resolveUIntOperand contextualType environment rightExpression
  decision <- mapLeft GrammarV1PlainUIntDivisionCoreError
    (checkPlainUIntDivision state coreOperator width left right result site)
  nextState <- case decision of
    PlainUIntDivisionEstablished _ -> Right state
    PlainUIntDivisionRequiresProof obligation ->
      mapLeft GrammarV1PlainUIntDivisionObligationError (emitObligation obligation state)
  Right (decision, nextState)

checkGrammarV1PlainSIntDivision
  :: CheckState
  -> GrammarV1Type
  -> GrammarV1SIntDivisionEnvironment
  -> GrammarV1Expression
  -> SIntTerm
  -> PlainIntegerDivisionSite
  -> Either
      GrammarV1PlainSIntDivisionError
      (PlainSIntDivisionDecision, CheckState)
checkGrammarV1PlainSIntDivision state contextualType environment expression result site = do
  ty <- case grammarV1PrimitiveType contextualType >>= sIntTypeFromCoreType of
    Just exactType -> Right exactType
    Nothing -> Left (GrammarV1PlainSIntDivisionContextRequired contextualType)
  (leftExpression, operator, rightExpression) <-
    mapLeft GrammarV1PlainSIntDivisionExpressionRequired
      (binaryParts expression)
  coreOperator <- mapLeft GrammarV1PlainSIntDivisionOperatorRequired
    (integerDivisionOperator operator)
  left <- resolveSIntOperand contextualType environment leftExpression
  right <- resolveSIntOperand contextualType environment rightExpression
  decision <- mapLeft GrammarV1PlainSIntDivisionCoreError
    (checkPlainSIntDivision state coreOperator ty left right result site)
  nextState <- case decision of
    PlainSIntDivisionEstablished _ -> Right state
    PlainSIntDivisionRequiresProof obligation ->
      mapLeft GrammarV1PlainSIntDivisionObligationError (emitObligation obligation state)
  Right (decision, nextState)

checkGrammarV1CheckedUIntDivision
  :: GrammarV1Type
  -> GrammarV1Expression
  -> ScalarLiteral
  -> ScalarLiteral
  -> Either
      GrammarV1CheckedDivisionSourceError
      (CheckedDivisionResult ScalarLiteral)
checkGrammarV1CheckedUIntDivision contextualType expression left right = do
  width <- case grammarV1PrimitiveType contextualType of
    Just (TyUInt exactWidth) -> Right exactWidth
    _ -> Left (GrammarV1CheckedUIntDivisionContextRequired contextualType)
  (_, operator, _) <- mapLeft GrammarV1CheckedDivisionExpressionRequired
    (binaryParts expression)
  coreOperator <- mapLeft GrammarV1CheckedDivisionOperatorRequired
    (integerDivisionOperator operator)
  mapLeft GrammarV1CheckedUIntDivisionCoreError
    (checkCheckedUIntDivision coreOperator width left right)

checkGrammarV1CheckedSIntDivision
  :: GrammarV1Type
  -> GrammarV1Expression
  -> SIntLiteral
  -> SIntLiteral
  -> Either
      GrammarV1CheckedDivisionSourceError
      (CheckedDivisionResult SIntLiteral)
checkGrammarV1CheckedSIntDivision contextualType expression left right = do
  ty <- case grammarV1PrimitiveType contextualType >>= sIntTypeFromCoreType of
    Just exactType -> Right exactType
    Nothing -> Left (GrammarV1CheckedSIntDivisionContextRequired contextualType)
  (_, operator, _) <- mapLeft GrammarV1CheckedDivisionExpressionRequired
    (binaryParts expression)
  coreOperator <- mapLeft GrammarV1CheckedDivisionOperatorRequired
    (integerDivisionOperator operator)
  mapLeft GrammarV1CheckedSIntDivisionCoreError
    (checkCheckedSIntDivision coreOperator ty left right)

binaryParts
  :: GrammarV1Expression
  -> Either GrammarV1Expression
      (GrammarV1Expression, GrammarV1BinaryOperator, GrammarV1Expression)
binaryParts expression = case expression of
  GrammarV1BinaryExpression left operator right ->
    Right (locatedValue left, locatedValue operator, locatedValue right)
  _ -> Left expression

integerDivisionOperator
  :: GrammarV1BinaryOperator
  -> Either GrammarV1BinaryOperator IntegerDivisionOperator
integerDivisionOperator operator = case operator of
  GrammarV1Divide -> Right IntegerQuotient
  GrammarV1Remainder -> Right IntegerRemainder
  _ -> Left operator

resolveUIntOperand
  :: GrammarV1Type
  -> GrammarV1UIntDivisionEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1PlainUIntDivisionError RefTerm
resolveUIntOperand contextualType environment expression = case expression of
  GrammarV1IntegerExpression _ -> do
    literal <- mapLeft GrammarV1PlainUIntDivisionLiteralError
      (grammarV1ContextualUIntLiteral contextualType expression)
    case literal of
      ScalarUIntLiteral width value -> Right (RefUInt width value)
      _ -> Left (GrammarV1PlainUIntDivisionLiteralIdentityMismatch literal)
  GrammarV1NameExpression reference arguments
    | null arguments -> case Map.lookup reference environment of
        Just term -> Right term
        Nothing -> Left (GrammarV1PlainUIntDivisionUnknownReference reference)
    | otherwise -> Left (GrammarV1PlainUIntDivisionUnsupportedOperand expression)
  _ -> Left (GrammarV1PlainUIntDivisionUnsupportedOperand expression)

resolveSIntOperand
  :: GrammarV1Type
  -> GrammarV1SIntDivisionEnvironment
  -> GrammarV1Expression
  -> Either GrammarV1PlainSIntDivisionError SIntTerm
resolveSIntOperand contextualType environment expression = case expression of
  GrammarV1IntegerExpression _ ->
    SIntKnown <$> mapLeft GrammarV1PlainSIntDivisionLiteralError
      (grammarV1ContextualSIntLiteral contextualType expression)
  GrammarV1NegateExpression _ ->
    SIntKnown <$> mapLeft GrammarV1PlainSIntDivisionLiteralError
      (grammarV1ContextualSIntLiteral contextualType expression)
  GrammarV1ParenthesizedExpression (Located _ inner) ->
    resolveSIntOperand contextualType environment inner
  GrammarV1NameExpression reference arguments
    | null arguments -> case Map.lookup reference environment of
        Just term -> Right term
        Nothing -> Left (GrammarV1PlainSIntDivisionUnknownReference reference)
    | otherwise -> Left (GrammarV1PlainSIntDivisionUnsupportedOperand expression)
  _ -> Left (GrammarV1PlainSIntDivisionUnsupportedOperand expression)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
