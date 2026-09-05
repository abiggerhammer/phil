{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.UIntArithmetic
  ( UIntArithmeticOperator (..)
  , PlainUIntArithmeticSite (..)
  , PlainUIntArithmeticDecision (..)
  , UIntArithmeticError (..)
  , checkPlainUIntArithmetic
  , plainUIntArithmeticProposition
  , registerUIntArithmeticClaims
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

-- | Runtime UInt arithmetic is mathematical arithmetic, not target arithmetic.
-- The operator therefore carries no wrap/saturate/trap mode.
data UIntArithmeticOperator
  = UIntAdd
  | UIntSubtract
  | UIntMultiply
  deriving (Eq, Ord, Show)

-- | Exact source/semantic location at which representability must hold.
data PlainUIntArithmeticSite = PlainUIntArithmeticSite
  { plainUIntArithmeticObligationId :: ObligationId
  , plainUIntArithmeticOrigin :: Text
  , plainUIntArithmeticScope :: Text
  , plainUIntArithmeticRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)

-- | A closed operation may be established immediately.  Otherwise plain
-- arithmetic produces an ordinary Core obligation; it never chooses a machine
-- overflow behavior.  ADR-025 competence decides what happens to that
-- obligation at the surrounding assurance boundary.
data PlainUIntArithmeticDecision
  = PlainUIntArithmeticEstablished ScalarLiteral
  | PlainUIntArithmeticRequiresProof Obligation
  deriving (Eq, Show)

data UIntArithmeticError
  = UIntArithmeticSortError SortError
  | UIntArithmeticOperandSortMismatch RefTerm RefSort Int
  | UIntArithmeticResultSortMismatch RefTerm RefSort Int
  | UIntArithmeticKnownResultOutOfRange
      UIntArithmeticOperator
      Int
      Integer
      Integer
      Integer
  | UIntArithmeticKnownResultMismatch
      UIntArithmeticOperator
      Int
      Integer
      Integer
      Integer
      Integer
  deriving (Eq, Show)

-- | Check one plain UInt[w] arithmetic step.
--
-- All three semantic terms must already have exact UInt[w] sort.  When all are
-- closed UInt literals, the mathematical result is computed using unbounded
-- Integer arithmetic and must equal the supplied result exactly and lie in
-- range.  No modulo reduction is ever performed.
--
-- For symbolic operands/result, this emits one exact ordinary Core obligation
-- whose opaque arithmetic claim is the semantic contract for this operation.
-- The claim arguments are width plus explicit UInt-to-Nat views of the exact
-- operands/result, so one claim declaration remains valid for every UInt width
-- without erasing width identity.  The existing discharge machinery may
-- prove/runtime-bind/export the obligation, while an unresolved obligation
-- remains an explicit failure.  A later checked-operation slice gives runtime
-- overflow/underflow its own source-visible outcome instead of laundering it
-- through this plain judgment.
checkPlainUIntArithmetic
  :: CheckState
  -> UIntArithmeticOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> PlainUIntArithmeticSite
  -> Either UIntArithmeticError PlainUIntArithmeticDecision
checkPlainUIntArithmetic state operator width left right result site = do
  checkOperand state width left
  checkOperand state width right
  checkResult state width result
  case (knownUInt left, knownUInt right, knownUInt result) of
    (Just (_, leftValue), Just (_, rightValue), Just (_, actualResult)) -> do
      let mathematicalResult = applyOperator operator leftValue rightValue
          literal = ScalarUIntLiteral width mathematicalResult
      if not (scalarLiteralInRange literal)
        then Left
          (UIntArithmeticKnownResultOutOfRange
            operator width leftValue rightValue mathematicalResult)
        else if actualResult /= mathematicalResult
          then Left
            (UIntArithmeticKnownResultMismatch
              operator width leftValue rightValue mathematicalResult actualResult)
          else Right (PlainUIntArithmeticEstablished literal)
    _ -> Right (PlainUIntArithmeticRequiresProof Obligation
      { obligationId = plainUIntArithmeticObligationId site
      , obligationProposition =
          plainUIntArithmeticProposition operator width left right result
      , obligationOrigin = plainUIntArithmeticOrigin site
      , obligationScope = plainUIntArithmeticScope site
      , obligationRequiredPoint = plainUIntArithmeticRequiredPoint site
      })

-- | Canonical proposition for one exact plain UInt operation.  Arithmetic claim
-- declarations are width-generic because all four claim parameters are Nat:
-- the explicit width plus exact toNat views of left/right/result.  The UInt
-- terms themselves remain exact semantic inputs to those views.
plainUIntArithmeticProposition
  :: UIntArithmeticOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> Proposition
plainUIntArithmeticProposition operator width left right result =
  Atom (operatorAtom operator)
    [ RefNat (toInteger width)
    , RefToNat left
    , RefToNat right
    , RefToNat result
    ]

-- | Install the three arithmetic relation declarations needed by Core focusing
-- before ADR-025 can reason about arithmetic obligations.  Re-registering the
-- exact same declarations is idempotent; a conflicting declaration under one
-- of the reserved arithmetic claim names fails closed as DuplicateClaim.
registerUIntArithmeticClaims
  :: StaticContext
  -> Either StaticError StaticContext
registerUIntArithmeticClaims context =
  foldM ensureClaim context [UIntAdd, UIntSubtract, UIntMultiply]
  where
    parameters =
      [ (Name "width", SortNat)
      , (Name "left", SortNat)
      , (Name "right", SortNat)
      , (Name "result", SortNat)
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
  -> Either UIntArithmeticError ()
checkOperand state width term = do
  actual <- mapLeft UIntArithmeticSortError (sortOfRefTerm state term)
  if actual == SortUInt width
    then Right ()
    else Left (UIntArithmeticOperandSortMismatch term actual width)

checkResult
  :: CheckState
  -> Int
  -> RefTerm
  -> Either UIntArithmeticError ()
checkResult state width term = do
  actual <- mapLeft UIntArithmeticSortError (sortOfRefTerm state term)
  if actual == SortUInt width
    then Right ()
    else Left (UIntArithmeticResultSortMismatch term actual width)

knownUInt :: RefTerm -> Maybe (Int, Integer)
knownUInt term = case term of
  RefUInt width value -> Just (width, value)
  _ -> Nothing

applyOperator :: UIntArithmeticOperator -> Integer -> Integer -> Integer
applyOperator operator left right = case operator of
  UIntAdd -> left + right
  UIntSubtract -> left - right
  UIntMultiply -> left * right

operatorAtom :: UIntArithmeticOperator -> Text
operatorAtom operator = case operator of
  UIntAdd -> "phil.uint.add.exact.v1"
  UIntSubtract -> "phil.uint.sub.exact.v1"
  UIntMultiply -> "phil.uint.mul.exact.v1"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
