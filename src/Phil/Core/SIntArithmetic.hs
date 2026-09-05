{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.SIntArithmetic
  ( SIntArithmeticOperator (..)
  , PlainSIntArithmeticSite (..)
  , PlainSIntArithmeticDecision (..)
  , SIntArithmeticError (..)
  , checkPlainSIntArithmetic
  , plainSIntArithmeticProposition
  , applySIntArithmeticOperator
  , registerSIntArithmeticClaims
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import Phil.Core.Checker (CheckState)
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  )
import Phil.Core.SortCheck
  ( SortError
  , sortOfRefTerm
  )
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  , StaticContext
  , StaticError (..)
  , declareOpaqueClaim
  , lookupClaim
  )
import Phil.Core.Syntax
  ( Name (..)
  , Obligation (..)
  , ObligationId
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )

-- | Runtime signed arithmetic is mathematical arithmetic. The source language
-- therefore has no hidden wrap, saturation, target trap, poison, or signed-UB
-- mode attached to an operator.
data SIntArithmeticOperator
  = SIntAdd
  | SIntSubtract
  | SIntMultiply
  deriving (Eq, Ord, Show)

data PlainSIntArithmeticSite = PlainSIntArithmeticSite
  { plainSIntArithmeticObligationId :: ObligationId
  , plainSIntArithmeticOrigin :: Text
  , plainSIntArithmeticScope :: Text
  , plainSIntArithmeticRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)

data PlainSIntArithmeticDecision
  = PlainSIntArithmeticEstablished ScalarLiteral
  | PlainSIntArithmeticRequiresProof Obligation
  deriving (Eq, Show)

data SIntArithmeticError
  = SIntArithmeticSortError SortError
  | SIntArithmeticOperandSortMismatch RefTerm RefSort Int
  | SIntArithmeticResultSortMismatch RefTerm RefSort Int
  | SIntArithmeticKnownResultOutOfRange
      SIntArithmeticOperator
      Int
      Integer
      Integer
      Integer
  | SIntArithmeticKnownResultMismatch
      SIntArithmeticOperator
      Int
      Integer
      Integer
      Integer
      Integer
  deriving (Eq, Show)

-- | Check one plain I[w] arithmetic step with unbounded Integer arithmetic.
-- Closed terms must equal the exact mathematical result and that result must be
-- representable in [-2^(w-1), 2^(w-1)-1]. Symbolic terms retain an ordinary Core
-- obligation instead of acquiring a target overflow convention.
checkPlainSIntArithmetic
  :: CheckState
  -> SIntArithmeticOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> PlainSIntArithmeticSite
  -> Either SIntArithmeticError PlainSIntArithmeticDecision
checkPlainSIntArithmetic state operator width left right result site = do
  checkOperand state width left
  checkOperand state width right
  checkResult state width result
  case (knownSInt left, knownSInt right, knownSInt result) of
    (Just (_, leftValue), Just (_, rightValue), Just (_, actualResult)) -> do
      let mathematicalResult = applySIntArithmeticOperator operator leftValue rightValue
          literal = ScalarSIntLiteral width mathematicalResult
      if not (scalarLiteralInRange literal)
        then Left
          (SIntArithmeticKnownResultOutOfRange
            operator width leftValue rightValue mathematicalResult)
        else if actualResult /= mathematicalResult
          then Left
            (SIntArithmeticKnownResultMismatch
              operator width leftValue rightValue mathematicalResult actualResult)
          else Right (PlainSIntArithmeticEstablished literal)
    _ -> Right (PlainSIntArithmeticRequiresProof Obligation
      { obligationId = plainSIntArithmeticObligationId site
      , obligationProposition =
          plainSIntArithmeticProposition operator width left right result
      , obligationOrigin = plainSIntArithmeticOrigin site
      , obligationScope = plainSIntArithmeticScope site
      , obligationRequiredPoint = plainSIntArithmeticRequiredPoint site
      })

-- | Width stays an exact Nat coordinate while values enter the mathematical
-- integer domain only through explicit RefToInteger views. This keeps one claim
-- declaration width-generic without erasing signedness from the source terms.
plainSIntArithmeticProposition
  :: SIntArithmeticOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> Proposition
plainSIntArithmeticProposition operator width left right result =
  Atom (operatorAtom operator)
    [ RefNat (toInteger width)
    , RefToInteger left
    , RefToInteger right
    , RefToInteger result
    ]

applySIntArithmeticOperator
  :: SIntArithmeticOperator
  -> Integer
  -> Integer
  -> Integer
applySIntArithmeticOperator operator left right = case operator of
  SIntAdd -> left + right
  SIntSubtract -> left - right
  SIntMultiply -> left * right

registerSIntArithmeticClaims
  :: StaticContext
  -> Either StaticError StaticContext
registerSIntArithmeticClaims context =
  foldM ensureClaim context [SIntAdd, SIntSubtract, SIntMultiply]
  where
    parameters =
      [ (Name "width", SortNat)
      , (Name "left", SortInteger)
      , (Name "right", SortInteger)
      , (Name "result", SortInteger)
      ]
    expected = ClaimDecl parameters OpaqueClaim

    ensureClaim current operator =
      let claimName = operatorAtom operator
      in case lookupClaim claimName current of
          Nothing -> declareOpaqueClaim claimName parameters current
          Just actual
            | actual == expected -> Right current
            | otherwise -> Left (DuplicateClaim claimName)

checkOperand
  :: CheckState
  -> Int
  -> RefTerm
  -> Either SIntArithmeticError ()
checkOperand state width term = do
  actual <- mapLeft SIntArithmeticSortError (sortOfRefTerm state term)
  if actual == SortSInt width
    then Right ()
    else Left (SIntArithmeticOperandSortMismatch term actual width)

checkResult
  :: CheckState
  -> Int
  -> RefTerm
  -> Either SIntArithmeticError ()
checkResult state width term = do
  actual <- mapLeft SIntArithmeticSortError (sortOfRefTerm state term)
  if actual == SortSInt width
    then Right ()
    else Left (SIntArithmeticResultSortMismatch term actual width)

knownSInt :: RefTerm -> Maybe (Int, Integer)
knownSInt term = case term of
  RefSInt width value -> Just (width, value)
  _ -> Nothing

operatorAtom :: SIntArithmeticOperator -> Text
operatorAtom operator = case operator of
  SIntAdd -> "phil.sint.add.exact.v1"
  SIntSubtract -> "phil.sint.sub.exact.v1"
  SIntMultiply -> "phil.sint.mul.exact.v1"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
