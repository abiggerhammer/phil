{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Checker (emptyCheckState)
import Phil.Core.IntegerDivision
  ( IntegerDivisionOperator (..)
  , PlainIntegerDivisionSite (..)
  , PlainSIntDivisionDecision (..)
  , SIntDivisionError (..)
  , checkCheckedSIntDivision
  , checkPlainSIntDivision
  )
import Phil.Core.NumericConversion
  ( NumericConversionError (..)
  , NumericType (..)
  , NumericValue (..)
  , convertNumericValue
  )
import Phil.Core.SIntArithmetic
  ( PlainSIntArithmeticDecision (..)
  , PlainSIntArithmeticSite (..)
  , SIntArithmeticError (..)
  , SIntArithmeticOperator (..)
  , SIntLiteral (..)
  , SIntTerm (..)
  , SIntType (..)
  , checkPlainSIntArithmetic
  )
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "REVIEW-R08 plain signed arithmetic rejects malformed left known operand"
        arithmeticLeftOutOfRange
    , test "REVIEW-R08 plain signed arithmetic rejects malformed right known operand"
        arithmeticRightOutOfRange
    , test "REVIEW-R08 plain signed arithmetic rejects malformed known result before proof"
        arithmeticResultOutOfRange
    , test "REVIEW-R08 plain signed arithmetic rejects malformed known operand before proof"
        arithmeticMalformedKnownBeforeProof
    , test "REVIEW-R08 plain signed arithmetic preserves exact I8 boundaries"
        arithmeticBoundaries
    , test "REVIEW-R08 plain signed division rejects malformed known dividend"
        divisionDividendOutOfRange
    , test "REVIEW-R08 plain signed division rejects malformed known result before proof"
        divisionResultOutOfRange
    , test "REVIEW-R08 plain signed division rejects malformed known operand before proof"
        divisionMalformedKnownBeforeProof
    , test "REVIEW-R08 plain signed division preserves exact I8 boundaries"
        divisionBoundaries
    , test "REVIEW-R08 checked signed division still rejects malformed raw literals"
        checkedDivisionControl
    , test "REVIEW-R08 numeric conversion still rejects malformed signed sources"
        conversionControl
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

arithmeticLeftOutOfRange :: Either String ()
arithmeticLeftOutOfRange =
  case checkPlainSIntArithmetic
      emptyCheckState SIntAdd i8
      (known 128) (known (-128)) (known 0) (arithSite "r8.arith.left") of
    Left (SIntArithmeticKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed left I8 operand was not rejected first: " <> show other)

arithmeticRightOutOfRange :: Either String ()
arithmeticRightOutOfRange =
  case checkPlainSIntArithmetic
      emptyCheckState SIntAdd i8
      (known 0) (known 128) (known (-128)) (arithSite "r8.arith.right") of
    Left (SIntArithmeticKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed right I8 operand was not rejected first: " <> show other)

arithmeticResultOutOfRange :: Either String ()
arithmeticResultOutOfRange =
  case checkPlainSIntArithmetic
      emptyCheckState SIntAdd i8
      (symbolic "left") (symbolic "right") (known 128)
      (arithSite "r8.arith.result") of
    Left (SIntArithmeticKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed known result became a proof obligation: " <> show other)

arithmeticMalformedKnownBeforeProof :: Either String ()
arithmeticMalformedKnownBeforeProof =
  case checkPlainSIntArithmetic
      emptyCheckState SIntMultiply i8
      (known 128) (symbolic "right") (symbolic "result")
      (arithSite "r8.arith.proof") of
    Left (SIntArithmeticKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed arithmetic operand became a proof obligation: " <> show other)

arithmeticBoundaries :: Either String ()
arithmeticBoundaries = do
  case checkPlainSIntArithmetic
      emptyCheckState SIntAdd i8
      (known (-128)) (known 0) (known (-128))
      (arithSite "r8.arith.min") of
    Right (PlainSIntArithmeticEstablished (SIntLiteral (SIntType 8) (-128))) -> Right ()
    other -> Left ("valid I8 minimum was rejected: " <> show other)
  case checkPlainSIntArithmetic
      emptyCheckState SIntAdd i8
      (known 127) (known 0) (known 127)
      (arithSite "r8.arith.max") of
    Right (PlainSIntArithmeticEstablished (SIntLiteral (SIntType 8) 127)) -> Right ()
    other -> Left ("valid I8 maximum was rejected: " <> show other)

divisionDividendOutOfRange :: Either String ()
divisionDividendOutOfRange =
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient i8
      (known 128) (known 2) (known 64) (divSite "r8.div.left") of
    Left (SIntDivisionKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed signed dividend was not rejected first: " <> show other)

divisionResultOutOfRange :: Either String ()
divisionResultOutOfRange =
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient i8
      (symbolic "left") (symbolic "right") (known 128)
      (divSite "r8.div.result") of
    Left (SIntDivisionKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed signed division result became a proof obligation: " <> show other)

divisionMalformedKnownBeforeProof :: Either String ()
divisionMalformedKnownBeforeProof =
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient i8
      (known 128) (symbolic "right") (symbolic "result")
      (divSite "r8.div.proof") of
    Left (SIntDivisionKnownTermOutOfRange (SIntLiteral (SIntType 8) 128)) -> Right ()
    other -> Left ("malformed signed division operand became a proof obligation: " <> show other)

divisionBoundaries :: Either String ()
divisionBoundaries = do
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient i8
      (known (-128)) (known 1) (known (-128))
      (divSite "r8.div.min") of
    Right (PlainSIntDivisionEstablished (SIntLiteral (SIntType 8) (-128))) -> Right ()
    other -> Left ("valid I8 minimum dividend was rejected: " <> show other)
  case checkPlainSIntDivision
      emptyCheckState IntegerQuotient i8
      (known 127) (known 1) (known 127)
      (divSite "r8.div.max") of
    Right (PlainSIntDivisionEstablished (SIntLiteral (SIntType 8) 127)) -> Right ()
    other -> Left ("valid I8 maximum dividend was rejected: " <> show other)

checkedDivisionControl :: Either String ()
checkedDivisionControl =
  case checkCheckedSIntDivision
      IntegerQuotient i8
      (literal 128) (literal 2) of
    Left _ -> Right ()
    other -> Left ("checked signed division stopped rejecting malformed input: " <> show other)

conversionControl :: Either String ()
conversionControl =
  case convertNumericValue
      (NumericSIntType i8)
      (NumericSIntValue (literal 128)) of
    Left (NumericConversionInvalidSource _) -> Right ()
    other -> Left ("numeric conversion stopped rejecting malformed signed source: " <> show other)

i8 :: SIntType
i8 = SIntType 8

literal :: Integer -> SIntLiteral
literal = SIntLiteral i8

known :: Integer -> SIntTerm
known = SIntKnown . literal

symbolic :: String -> SIntTerm
symbolic = SIntSymbolic i8 . fromStringText

fromStringText :: String -> Data.Text.Text
fromStringText = Data.Text.pack

arithSite :: Data.Text.Text -> PlainSIntArithmeticSite
arithSite identifier = PlainSIntArithmeticSite
  { plainSIntArithmeticObligationId = ObligationId identifier
  , plainSIntArithmeticOrigin = "REVIEW-R08"
  , plainSIntArithmeticScope = "raw signed arithmetic API"
  , plainSIntArithmeticRequiredPoint = "before accepting any raw known term"
  }

divSite :: Data.Text.Text -> PlainIntegerDivisionSite
divSite identifier = PlainIntegerDivisionSite
  { plainIntegerDivisionObligationId = ObligationId identifier
  , plainIntegerDivisionOrigin = "REVIEW-R08"
  , plainIntegerDivisionScope = "raw signed division API"
  , plainIntegerDivisionRequiredPoint = "before accepting any raw known term"
  }
