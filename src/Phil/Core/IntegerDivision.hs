{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.IntegerDivision
  ( IntegerDivisionOperator (..)
  , PlainIntegerDivisionSite (..)
  , PlainUIntDivisionDecision (..)
  , PlainSIntDivisionDecision (..)
  , UIntDivisionError (..)
  , SIntDivisionError (..)
  , CheckedDivisionResult (..)
  , CheckedUIntDivisionError (..)
  , CheckedSIntDivisionError (..)
  , checkedIntegerDivideByZeroFailure
  , checkedSignedDivisionOverflowFailure
  , checkedUIntDivisionFailures
  , checkedSIntDivisionFailures
  , checkPlainUIntDivision
  , checkPlainSIntDivision
  , checkCheckedUIntDivision
  , checkCheckedSIntDivision
  , plainUIntDivisionProposition
  , plainSIntDivisionProposition
  , signedQuotientRemainder
  , registerIntegerDivisionClaims
  ) where

import Control.Monad (foldM)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Checker (CheckState)
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  )
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntTerm (..)
  , SIntType (..)
  , sIntLiteralInRange
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
  , Outcome (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )

-- | Integer quotient and remainder are one paired semantic family. For signed
-- values the quotient truncates toward zero and the remainder is defined by
-- a = q*b + r, so r is zero or has the dividend's sign.
data IntegerDivisionOperator
  = IntegerQuotient
  | IntegerRemainder
  deriving (Eq, Ord, Show)

data PlainIntegerDivisionSite = PlainIntegerDivisionSite
  { plainIntegerDivisionObligationId :: ObligationId
  , plainIntegerDivisionOrigin :: Text
  , plainIntegerDivisionScope :: Text
  , plainIntegerDivisionRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)

data PlainUIntDivisionDecision
  = PlainUIntDivisionEstablished ScalarLiteral
  | PlainUIntDivisionRequiresProof Obligation
  deriving (Eq, Show)

data PlainSIntDivisionDecision
  = PlainSIntDivisionEstablished SIntLiteral
  | PlainSIntDivisionRequiresProof Obligation
  deriving (Eq, Show)

data UIntDivisionError
  = UIntDivisionSortError SortError
  | UIntDivisionOperandSortMismatch RefTerm RefSort Int
  | UIntDivisionResultSortMismatch RefTerm RefSort Int
  | UIntDivisionKnownZeroDivisor Int Integer
  | UIntDivisionKnownResultMismatch
      IntegerDivisionOperator Int Integer Integer Integer Integer
  deriving (Eq, Show)

data SIntDivisionError
  = SIntDivisionInvalidWidth Int
  | SIntDivisionOperandTypeMismatch SIntTerm SIntType
  | SIntDivisionResultTypeMismatch SIntTerm SIntType
  | SIntDivisionEmptySymbolicIdentity SIntTerm
  | SIntDivisionKnownZeroDivisor Int Integer
  | SIntDivisionKnownResultOutOfRange
      IntegerDivisionOperator Int Integer Integer Integer
  | SIntDivisionKnownResultMismatch
      IntegerDivisionOperator Int Integer Integer Integer Integer
  deriving (Eq, Show)

data CheckedDivisionResult a
  = CheckedDivisionSucceeded a Proposition
  | CheckedDivisionNegative CallableFailure
  deriving (Eq, Show)

data CheckedUIntDivisionError
  = CheckedUIntDivisionInvalidWidth Int
  | CheckedUIntDivisionOperandTypeMismatch ScalarLiteral Int
  | CheckedUIntDivisionOperandOutOfRange ScalarLiteral
  deriving (Eq, Show)

data CheckedSIntDivisionError
  = CheckedSIntDivisionInvalidWidth Int
  | CheckedSIntDivisionOperandTypeMismatch SIntLiteral SIntType
  | CheckedSIntDivisionOperandOutOfRange SIntLiteral
  deriving (Eq, Show)

checkedIntegerDivideByZeroFailure :: CallableFailure
checkedIntegerDivideByZeroFailure =
  CallableTypedNegative (Outcome "integer-divide-by-zero")

checkedSignedDivisionOverflowFailure :: CallableFailure
checkedSignedDivisionOverflowFailure =
  CallableTypedNegative (Outcome "signed-division-overflow")

checkedUIntDivisionFailures :: IntegerDivisionOperator -> Set.Set CallableFailure
checkedUIntDivisionFailures _ = Set.singleton checkedIntegerDivideByZeroFailure

checkedSIntDivisionFailures :: IntegerDivisionOperator -> Set.Set CallableFailure
checkedSIntDivisionFailures operator = case operator of
  IntegerQuotient -> Set.fromList
    [ checkedIntegerDivideByZeroFailure
    , checkedSignedDivisionOverflowFailure
    ]
  IntegerRemainder -> Set.singleton checkedIntegerDivideByZeroFailure

-- | Plain UInt quotient/remainder is admitted only when the exact semantic
-- relation is established. A closed zero divisor rejects immediately; a
-- symbolic operation carries one ordinary proof obligation whose claim includes
-- nonzero-divisor and exact quotient/remainder semantics.
checkPlainUIntDivision
  :: CheckState
  -> IntegerDivisionOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> PlainIntegerDivisionSite
  -> Either UIntDivisionError PlainUIntDivisionDecision
checkPlainUIntDivision state operator width left right result site = do
  checkUIntOperand state width left
  checkUIntOperand state width right
  checkUIntResult state width result
  case (knownUInt left, knownUInt right, knownUInt result) of
    (Just leftValue, Just 0, _) ->
      Left (UIntDivisionKnownZeroDivisor width leftValue)
    (Just leftValue, Just rightValue, Just actualResult) -> do
      let mathematicalResult = unsignedDivisionResult operator leftValue rightValue
      if actualResult == mathematicalResult
        then Right (PlainUIntDivisionEstablished
          (ScalarUIntLiteral width mathematicalResult))
        else Left (UIntDivisionKnownResultMismatch
          operator width leftValue rightValue mathematicalResult actualResult)
    _ -> Right (PlainUIntDivisionRequiresProof (siteObligation site
      (plainUIntDivisionProposition operator width left right result)))

-- | Plain signed quotient/remainder uses a target-independent truncation-toward-
-- zero definition. The only nonzero-divisor representability failure is the
-- minimum signed value divided by -1 on the quotient path; it rejects rather
-- than becoming target overflow, poison, or a trap.
checkPlainSIntDivision
  :: CheckState
  -> IntegerDivisionOperator
  -> SIntType
  -> SIntTerm
  -> SIntTerm
  -> SIntTerm
  -> PlainIntegerDivisionSite
  -> Either SIntDivisionError PlainSIntDivisionDecision
checkPlainSIntDivision _state operator ty@(SIntType width) left right result site = do
  if width > 0 then Right () else Left (SIntDivisionInvalidWidth width)
  checkSIntTerm SIntDivisionOperandTypeMismatch ty left
  checkSIntTerm SIntDivisionOperandTypeMismatch ty right
  checkSIntTerm SIntDivisionResultTypeMismatch ty result
  case (knownSInt left, knownSInt right, knownSInt result) of
    (Just leftValue, Just 0, _) ->
      Left (SIntDivisionKnownZeroDivisor width leftValue)
    (Just leftValue, Just rightValue, Just actualResult) -> do
      let (quotient, remainder) = signedQuotientRemainder leftValue rightValue
          mathematicalResult = case operator of
            IntegerQuotient -> quotient
            IntegerRemainder -> remainder
          literal = SIntLiteral ty mathematicalResult
      if not (sIntLiteralInRange literal)
        then Left (SIntDivisionKnownResultOutOfRange
          operator width leftValue rightValue mathematicalResult)
        else if actualResult /= mathematicalResult
          then Left (SIntDivisionKnownResultMismatch
            operator width leftValue rightValue mathematicalResult actualResult)
          else Right (PlainSIntDivisionEstablished literal)
    _ -> Right (PlainSIntDivisionRequiresProof (siteObligation site
      (plainSIntDivisionProposition operator ty left right result)))

checkCheckedUIntDivision
  :: IntegerDivisionOperator
  -> Int
  -> ScalarLiteral
  -> ScalarLiteral
  -> Either CheckedUIntDivisionError (CheckedDivisionResult ScalarLiteral)
checkCheckedUIntDivision operator width leftLiteral rightLiteral = do
  if width > 0 then Right () else Left (CheckedUIntDivisionInvalidWidth width)
  left <- checkedUIntValue leftLiteral
  right <- checkedUIntValue rightLiteral
  if right == 0
    then Right (CheckedDivisionNegative checkedIntegerDivideByZeroFailure)
    else
      let result = unsignedDivisionResult operator left right
          literal = ScalarUIntLiteral width result
          proposition = plainUIntDivisionProposition
            operator width (RefUInt width left) (RefUInt width right) (RefUInt width result)
      in Right (CheckedDivisionSucceeded literal proposition)
  where
    checkedUIntValue literal = case literal of
      ScalarUIntLiteral actualWidth value
        | actualWidth /= width -> Left (CheckedUIntDivisionOperandTypeMismatch literal width)
        | not (scalarLiteralInRange literal) -> Left (CheckedUIntDivisionOperandOutOfRange literal)
        | otherwise -> Right value
      _ -> Left (CheckedUIntDivisionOperandTypeMismatch literal width)

checkCheckedSIntDivision
  :: IntegerDivisionOperator
  -> SIntType
  -> SIntLiteral
  -> SIntLiteral
  -> Either CheckedSIntDivisionError (CheckedDivisionResult SIntLiteral)
checkCheckedSIntDivision operator ty@(SIntType width) leftLiteral rightLiteral = do
  if width > 0 then Right () else Left (CheckedSIntDivisionInvalidWidth width)
  left <- checkedSIntValue leftLiteral
  right <- checkedSIntValue rightLiteral
  if right == 0
    then Right (CheckedDivisionNegative checkedIntegerDivideByZeroFailure)
    else
      let (quotient, remainder) = signedQuotientRemainder left right
          result = case operator of
            IntegerQuotient -> quotient
            IntegerRemainder -> remainder
          literal = SIntLiteral ty result
      in if sIntLiteralInRange literal
          then Right (CheckedDivisionSucceeded literal
            (plainSIntDivisionProposition operator ty
              (SIntKnown leftLiteral)
              (SIntKnown rightLiteral)
              (SIntKnown literal)))
          else Right (CheckedDivisionNegative checkedSignedDivisionOverflowFailure)
  where
    checkedSIntValue literal
      | sIntLiteralType literal /= ty =
          Left (CheckedSIntDivisionOperandTypeMismatch literal ty)
      | not (sIntLiteralInRange literal) =
          Left (CheckedSIntDivisionOperandOutOfRange literal)
      | otherwise = Right (sIntLiteralValue literal)

plainUIntDivisionProposition
  :: IntegerDivisionOperator
  -> Int
  -> RefTerm
  -> RefTerm
  -> RefTerm
  -> Proposition
plainUIntDivisionProposition operator width left right result =
  Atom (uintOperatorAtom operator)
    [ RefNat (toInteger width)
    , RefToNat left
    , RefToNat right
    , RefToNat result
    ]

plainSIntDivisionProposition
  :: IntegerDivisionOperator
  -> SIntType
  -> SIntTerm
  -> SIntTerm
  -> SIntTerm
  -> Proposition
plainSIntDivisionProposition operator ty@(SIntType width) left right result =
  Atom (sintOperatorAtom operator)
    [ RefNat (toInteger width)
    , encodeSIntTerm ty left
    , encodeSIntTerm ty right
    , encodeSIntTerm ty result
    ]

-- | Define signed quotient without relying on a host signed-division rule: divide
-- absolute values in Nat, restore the quotient sign, then derive the paired
-- remainder from a = q*b + r. This yields truncation toward zero and the
-- dividend-sign remainder rule for every nonzero divisor.
signedQuotientRemainder :: Integer -> Integer -> (Integer, Integer)
signedQuotientRemainder dividend divisor
  | divisor == 0 = error "signedQuotientRemainder: zero divisor"
  | otherwise =
      let magnitude = abs dividend `div` abs divisor
          quotient = if (dividend < 0) /= (divisor < 0)
            then negate magnitude
            else magnitude
          remainder = dividend - quotient * divisor
      in (quotient, remainder)

registerIntegerDivisionClaims :: StaticContext -> Either StaticError StaticContext
registerIntegerDivisionClaims context =
  foldM ensureClaim context
    [ uintOperatorAtom IntegerQuotient
    , uintOperatorAtom IntegerRemainder
    , sintOperatorAtom IntegerQuotient
    , sintOperatorAtom IntegerRemainder
    ]
  where
    parameters =
      [ (Name "width", SortNat)
      , (Name "left", SortNat)
      , (Name "right", SortNat)
      , (Name "result", SortNat)
      ]
    expected = ClaimDecl parameters OpaqueClaim
    ensureClaim current claimName = case lookupClaim claimName current of
      Nothing -> declareOpaqueClaim claimName parameters current
      Just actual
        | actual == expected -> Right current
        | otherwise -> Left (DuplicateClaim claimName)

siteObligation :: PlainIntegerDivisionSite -> Proposition -> Obligation
siteObligation site proposition = Obligation
  { obligationId = plainIntegerDivisionObligationId site
  , obligationProposition = proposition
  , obligationOrigin = plainIntegerDivisionOrigin site
  , obligationScope = plainIntegerDivisionScope site
  , obligationRequiredPoint = plainIntegerDivisionRequiredPoint site
  }

unsignedDivisionResult :: IntegerDivisionOperator -> Integer -> Integer -> Integer
unsignedDivisionResult operator left right = case operator of
  IntegerQuotient -> left `div` right
  IntegerRemainder -> left `mod` right

checkUIntOperand :: CheckState -> Int -> RefTerm -> Either UIntDivisionError ()
checkUIntOperand state width term = do
  actual <- mapLeft UIntDivisionSortError (sortOfRefTerm state term)
  if actual == SortUInt width
    then Right ()
    else Left (UIntDivisionOperandSortMismatch term actual width)

checkUIntResult :: CheckState -> Int -> RefTerm -> Either UIntDivisionError ()
checkUIntResult state width term = do
  actual <- mapLeft UIntDivisionSortError (sortOfRefTerm state term)
  if actual == SortUInt width
    then Right ()
    else Left (UIntDivisionResultSortMismatch term actual width)

knownUInt :: RefTerm -> Maybe Integer
knownUInt term = case term of
  RefUInt _ value -> Just value
  _ -> Nothing

checkSIntTerm
  :: (SIntTerm -> SIntType -> SIntDivisionError)
  -> SIntType
  -> SIntTerm
  -> Either SIntDivisionError ()
checkSIntTerm mismatch expected term = do
  if sIntTermType term == expected then Right () else Left (mismatch term expected)
  case term of
    SIntSymbolic _ identity
      | Text.null (Text.strip identity) -> Left (SIntDivisionEmptySymbolicIdentity term)
    _ -> Right ()

sIntTermType :: SIntTerm -> SIntType
sIntTermType term = case term of
  SIntKnown literal -> sIntLiteralType literal
  SIntSymbolic ty _ -> ty

knownSInt :: SIntTerm -> Maybe Integer
knownSInt term = case term of
  SIntKnown literal -> Just (sIntLiteralValue literal)
  SIntSymbolic {} -> Nothing

encodeSIntTerm :: SIntType -> SIntTerm -> RefTerm
encodeSIntTerm ty@(SIntType width) term = case term of
  SIntKnown literal -> RefNat (sIntLiteralValue literal + 2 ^ (width - 1))
  SIntSymbolic _ identity ->
    RefOpaque SortNat ("phil.sint.bias.v1:I" <> Text.pack (show width) <> ":" <> identity)

uintOperatorAtom :: IntegerDivisionOperator -> Text
uintOperatorAtom operator = case operator of
  IntegerQuotient -> "phil.uint.quot.exact.v1"
  IntegerRemainder -> "phil.uint.rem.exact.v1"

sintOperatorAtom :: IntegerDivisionOperator -> Text
sintOperatorAtom operator = case operator of
  IntegerQuotient -> "phil.sint.quot.exact.v1"
  IntegerRemainder -> "phil.sint.rem.exact.v1"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
