{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.IntegerDivision
  ( CheckedDivisionResult (..)
  , IntegerDivisionOperator (..)
  , PlainIntegerDivisionSite (..)
  , PlainSIntDivisionDecision (..)
  , PlainUIntDivisionDecision (..)
  , SIntDivisionError (..)
  , UIntDivisionError (..)
  , checkCheckedSIntDivision
  , checkCheckedUIntDivision
  , checkPlainSIntDivision
  , checkPlainUIntDivision
  , checkedIntegerDivideByZeroFailure
  , checkedSIntDivisionFailures
  , checkedSignedDivisionOverflowFailure
  , checkedUIntDivisionFailures
  , plainSIntDivisionProposition
  , plainUIntDivisionProposition
  , signedQuotientRemainder
  )
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.SIntArithmetic
  ( SIntLiteral (..)
  , SIntTerm (..)
  , SIntType (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , RefSort (..)
  , RefTerm (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-017 unsigned quotient/remainder are exact" unsignedExact
    , test "EXEC-017 signed quotient truncates toward zero" signedQuotientSigns
    , test "EXEC-017 signed remainder has dividend sign" signedRemainderSigns
    , test "EXEC-017 plain zero divisor rejects" plainZeroDivisorRejects
    , test "EXEC-017 checked zero divisor is typed-negative" checkedZeroDivisor
    , test "EXEC-017 minInt / -1 cannot overflow silently" signedMinimumOverflow
    , test "EXEC-017 minInt % -1 remains exact zero" signedMinimumRemainder
    , test "EXEC-017 symbolic UInt division retains exact obligation" symbolicUIntObligation
    , test "EXEC-017 symbolic signed remainder retains exact obligation" symbolicSIntObligation
    , test "EXEC-017 checked failure sets are operator-exact" checkedFailureSets
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

unsignedExact :: Either String ()
unsignedExact = do
  quotient <- mapLeft show $ checkPlainUIntDivision
    emptyCheckState IntegerQuotient 8
    (RefUInt 8 7) (RefUInt 8 3) (RefUInt 8 2) (site "exec017.uint.quot")
  remainder <- mapLeft show $ checkPlainUIntDivision
    emptyCheckState IntegerRemainder 8
    (RefUInt 8 7) (RefUInt 8 3) (RefUInt 8 1) (site "exec017.uint.rem")
  assert
    (quotient == PlainUIntDivisionEstablished (ScalarUIntLiteral 8 2))
    ("unexpected U8 quotient: " <> show quotient)
  assert
    (remainder == PlainUIntDivisionEstablished (ScalarUIntLiteral 8 1))
    ("unexpected U8 remainder: " <> show remainder)

signedQuotientSigns :: Either String ()
signedQuotientSigns = mapM_ check
  [ (7, 3, 2)
  , (-7, 3, -2)
  , (7, -3, -2)
  , (-7, -3, 2)
  ]
  where
    check (left, right, expected) = do
      let (quotient, _) = signedQuotientRemainder left right
      assert (quotient == expected)
        ("quotient mismatch for " <> show (left, right, quotient, expected))

signedRemainderSigns :: Either String ()
signedRemainderSigns = mapM_ check
  [ (7, 3, 1)
  , (-7, 3, -1)
  , (7, -3, 1)
  , (-7, -3, -1)
  ]
  where
    check (left, right, expected) = do
      let (quotient, remainder) = signedQuotientRemainder left right
      assert (remainder == expected)
        ("remainder mismatch for " <> show (left, right, remainder, expected))
      assert (left == quotient * right + remainder)
        ("a = q*b + r failed for " <> show (left, right, quotient, remainder))
      assert (abs remainder < abs right)
        ("remainder magnitude bound failed for " <> show (left, right, remainder))
      assert (remainder == 0 || signum remainder == signum left)
        ("remainder sign is not dividend sign for " <> show (left, right, remainder))

plainZeroDivisorRejects :: Either String ()
plainZeroDivisorRejects = do
  case checkPlainUIntDivision
      emptyCheckState IntegerQuotient 8
      (RefUInt 8 9) (RefUInt 8 0) (RefUInt 8 0) (site "exec017.uint.zero") of
    Left (UIntDivisionKnownZeroDivisor 8 9) -> Right ()
    other -> Left ("plain UInt zero divisor did not reject: " <> show other)
  let ty = SIntType 8
  case checkPlainSIntDivision
      emptyCheckState IntegerRemainder ty
      (knownS 8 (-9)) (knownS 8 0) (knownS 8 0) (site "exec017.sint.zero") of
    Left (SIntDivisionKnownZeroDivisor 8 (-9)) -> Right ()
    other -> Left ("plain signed zero divisor did not reject: " <> show other)

checkedZeroDivisor :: Either String ()
checkedZeroDivisor = do
  uintDecision <- mapLeft show $ checkCheckedUIntDivision
    IntegerQuotient 8 (ScalarUIntLiteral 8 9) (ScalarUIntLiteral 8 0)
  assert
    (uintDecision == CheckedDivisionNegative checkedIntegerDivideByZeroFailure)
    ("checked UInt zero divisor changed outcome: " <> show uintDecision)
  let ty = SIntType 8
  sintDecision <- mapLeft show $ checkCheckedSIntDivision
    IntegerRemainder ty (SIntLiteral ty (-9)) (SIntLiteral ty 0)
  assert
    (sintDecision == CheckedDivisionNegative checkedIntegerDivideByZeroFailure)
    ("checked signed zero divisor changed outcome: " <> show sintDecision)

signedMinimumOverflow :: Either String ()
signedMinimumOverflow = do
  let ty = SIntType 8
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient ty
      (knownS 8 (-128)) (knownS 8 (-1)) (knownS 8 (-128))
      (site "exec017.sint.min-overflow") of
    Left (SIntDivisionKnownResultOutOfRange IntegerQuotient 8 (-128) (-1) 128) -> Right ()
    other -> Left ("plain minInt/-1 did not reject: " <> show other)
  checked <- mapLeft show $ checkCheckedSIntDivision
    IntegerQuotient ty (SIntLiteral ty (-128)) (SIntLiteral ty (-1))
  assert
    (checked == CheckedDivisionNegative checkedSignedDivisionOverflowFailure)
    ("checked minInt/-1 did not select overflow branch: " <> show checked)

signedMinimumRemainder :: Either String ()
signedMinimumRemainder = do
  let ty = SIntType 8
  plain <- mapLeft show $ checkPlainSIntDivision
    emptyCheckState IntegerRemainder ty
    (knownS 8 (-128)) (knownS 8 (-1)) (knownS 8 0)
    (site "exec017.sint.min-rem")
  assert
    (plain == PlainSIntDivisionEstablished (SIntLiteral ty 0))
    ("minInt%-1 should be exact zero: " <> show plain)
  checked <- mapLeft show $ checkCheckedSIntDivision
    IntegerRemainder ty (SIntLiteral ty (-128)) (SIntLiteral ty (-1))
  case checked of
    CheckedDivisionSucceeded literal _ ->
      assert (literal == SIntLiteral ty 0)
        ("checked minInt%-1 changed result: " <> show literal)
    other -> Left ("checked minInt%-1 unexpectedly failed: " <> show other)

symbolicUIntObligation :: Either String ()
symbolicUIntObligation = do
  let left = RefOpaque (SortUInt 16) "exec017.uint.left"
      right = RefOpaque (SortUInt 16) "exec017.uint.right"
      result = RefOpaque (SortUInt 16) "exec017.uint.result"
  decision <- mapLeft show $ checkPlainUIntDivision
    emptyCheckState IntegerQuotient 16 left right result (site "exec017.uint.symbolic")
  obligation <- case decision of
    PlainUIntDivisionRequiresProof value -> Right value
    other -> Left ("symbolic UInt division did not retain obligation: " <> show other)
  assert
    (obligationProposition obligation
      == plainUIntDivisionProposition IntegerQuotient 16 left right result)
    "symbolic UInt quotient proposition changed"

symbolicSIntObligation :: Either String ()
symbolicSIntObligation = do
  let ty = SIntType 32
      left = SIntSymbolic ty "exec017.sint.left"
      right = SIntSymbolic ty "exec017.sint.right"
      result = SIntSymbolic ty "exec017.sint.result"
  decision <- mapLeft show $ checkPlainSIntDivision
    emptyCheckState IntegerRemainder ty left right result (site "exec017.sint.symbolic")
  obligation <- case decision of
    PlainSIntDivisionRequiresProof value -> Right value
    other -> Left ("symbolic signed remainder did not retain obligation: " <> show other)
  assert
    (obligationProposition obligation
      == plainSIntDivisionProposition IntegerRemainder ty left right result)
    "symbolic signed remainder proposition changed"

checkedFailureSets :: Either String ()
checkedFailureSets = do
  assert
    (checkedUIntDivisionFailures IntegerQuotient
      == Set.singleton checkedIntegerDivideByZeroFailure)
    "UInt checked division acquired an undeclared failure"
  assert
    (checkedSIntDivisionFailures IntegerQuotient
      == Set.fromList [checkedIntegerDivideByZeroFailure, checkedSignedDivisionOverflowFailure])
    "signed checked quotient failure set is incomplete or widened"
  assert
    (checkedSIntDivisionFailures IntegerRemainder
      == Set.singleton checkedIntegerDivideByZeroFailure)
    "signed checked remainder should not expose quotient overflow"

knownS :: Int -> Integer -> SIntTerm
knownS width value =
  let ty = SIntType width
  in SIntKnown (SIntLiteral ty value)

site :: Text -> PlainIntegerDivisionSite
site identifier = PlainIntegerDivisionSite
  { plainIntegerDivisionObligationId = ObligationId identifier
  , plainIntegerDivisionOrigin = "EXEC-017"
  , plainIntegerDivisionScope = "fixed-width integer division"
  , plainIntegerDivisionRequiredPoint = "before quotient/remainder result use"
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
