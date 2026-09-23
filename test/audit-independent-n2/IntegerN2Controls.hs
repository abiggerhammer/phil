{-# LANGUAGE OverloadedStrings #-}
-- First-party correctness controls for the original Phil Phase 1 candidate.
-- Prepared, NOT compiled or executed by the audit. Setup failure is not rejection.
module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), CheckerError (..), emptyCheckState)
import qualified Phil.Core.CheckedUIntArithmetic as CU
import qualified Phil.Core.IntegerDivision as D
import qualified Phil.Core.IntegerShift as H
import qualified Phil.Core.NumericConversion as N
import Phil.Core.Scalar (ScalarLiteral (..))
import qualified Phil.Core.SIntArithmetic as S
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Syntax (Obligation (..), ObligationId (..), Proposition (..), RefSort (..), RefTerm (..))
import qualified Phil.Core.UIntArithmetic as U
import qualified Phil.Surface.GrammarV1.IntegerDivision as SD
import qualified Phil.Surface.GrammarV1.NumericConversion as E
import qualified Phil.Surface.GrammarV1.SIntArithmetic as SA
import qualified Phil.Surface.GrammarV1.UIntArithmetic as UA
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1BinaryOperator (..), GrammarV1Block (..), GrammarV1ComponentDecl (..), GrammarV1Declaration (..)
  , GrammarV1Expression (..), GrammarV1QualifiedName (..), GrammarV1SourceFile (..)
  , GrammarV1Statement (..), GrammarV1StaticReference (..), GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..), parseGrammarV1StructuralSource )
import Phil.Surface.Syntax (Located (..))
import System.Environment (getArgs)
import System.Exit (exitFailure, exitWith, ExitCode (..))

data Failure = Setup String | Mismatch String deriving Show
type Check = Either Failure ()

main :: IO ()
main = do
  args <- getArgs
  let selected = if args == ["--observations"] then observations else controls
  unless (null args || args == ["--observations"]) $ do
    putStrLn "usage: IntegerN2Controls [--observations]"
    exitWith (ExitFailure 2)
  results <- mapM run selected
  putStrLn ("N2_DONE " ++ show (length selected))
  unless (and results) exitFailure
  where
    run (key, check) = do
      evaluated <- try (evaluate check) :: IO (Either SomeException Check)
      case evaluated of
        Left err -> putStrLn ("N2_ERROR " ++ key ++ " " ++ show err) >> pure False
        Right (Left (Setup detail)) -> putStrLn ("N2_ERROR " ++ key ++ " " ++ detail) >> pure False
        Right (Left (Mismatch detail)) -> putStrLn ("N2_FAIL " ++ key ++ " " ++ detail) >> pure False
        Right (Right ()) -> putStrLn ("N2_PASS " ++ key) >> pure True

same :: (Eq a, Show a) => a -> a -> Check
same expected actual = unless (expected == actual) $
  Left (Mismatch ("expected " ++ show expected ++ "; got " ++ show actual))
truth :: String -> Bool -> Check
truth label yes = unless yes (Left (Mismatch label))
setup :: Show a => Either a b -> Either Failure b
setup = either (Left . Setup . show) Right
expectRight :: Show a => Either a b -> Either Failure b
expectRight = either (Left . Mismatch . ("expected success, got ") . show) Right

uFits :: Int -> Integer -> Bool
uFits w n = w > 0 && 0 <= n && n < 2 ^ w
iFits :: Int -> Integer -> Bool
iFits w n = w > 0 && negate (2 ^ (w-1)) <= n && n < 2 ^ (w-1)
uValues :: Int -> [Integer]
uValues w = [0 .. 2 ^ w - 1]
iValues :: Int -> [Integer]
iValues w = [negate (2 ^ (w-1)) .. 2 ^ (w-1) - 1]
sl :: Int -> Integer -> S.SIntLiteral
sl w = S.SIntLiteral (S.SIntType w)
sk :: Int -> Integer -> S.SIntTerm
sk w = S.SIntKnown . sl w
nv :: Int -> Integer -> N.NumericValue
nv w = N.NumericSIntValue . sl w

uOps :: [(U.UIntArithmeticOperator, Text, Integer -> Integer -> Integer)]
uOps = [(U.UIntAdd,"add",(+)),(U.UIntSubtract,"sub",(-)),(U.UIntMultiply,"mul",(*))]
sOps :: [(S.SIntArithmeticOperator, Text, Integer -> Integer -> Integer)]
sOps = [(S.SIntAdd,"add",(+)),(S.SIntSubtract,"sub",(-)),(S.SIntMultiply,"mul",(*))]
dOps :: [(D.IntegerDivisionOperator, Text)]
dOps = [(D.IntegerQuotient,"quot"),(D.IntegerRemainder,"rem")]

uProp :: Text -> Int -> Integer -> Integer -> Integer -> Proposition
uProp op w a b r = Atom ("phil.uint." <> op <> ".exact.v1")
  [RefNat (toInteger w),RefToNat (RefUInt w a),RefToNat (RefUInt w b),RefToNat (RefUInt w r)]
iProp :: Text -> Int -> Integer -> Integer -> Integer -> Proposition
iProp op w a b r = Atom ("phil.sint." <> op <> ".exact.v1")
  [RefNat (toInteger w),RefNat (a+offset),RefNat (b+offset),RefNat (r+offset)]
  where offset = 2 ^ (w-1)

uSite :: U.PlainUIntArithmeticSite
uSite = U.PlainUIntArithmeticSite (ObligationId "n2.uint") "origin.n2" "scope.n2" "point.n2"
sSite :: S.PlainSIntArithmeticSite
sSite = S.PlainSIntArithmeticSite (ObligationId "n2.sint") "origin.n2" "scope.n2" "point.n2"
dSite :: D.PlainIntegerDivisionSite
dSite = D.PlainIntegerDivisionSite (ObligationId "n2.div") "origin.n2" "scope.n2" "point.n2"
expectedOb :: Text -> Proposition -> Obligation
expectedOb key prop = Obligation
  { obligationId=ObligationId key, obligationProposition=prop
  , obligationOrigin="origin.n2", obligationScope="scope.n2", obligationRequiredPoint="point.n2" }
ux, uy, ur :: RefTerm
ux = RefOpaque (SortUInt 8) "x"
uy = RefOpaque (SortUInt 8) "y"
ur = RefOpaque (SortUInt 8) "r"
sx, sy, sr :: S.SIntTerm
sx = S.SIntSymbolic (S.SIntType 8) "x"
sy = S.SIntSymbolic (S.SIntType 8) "y"
sr = S.SIntSymbolic (S.SIntType 8) "r"

-- Independent expected arithmetic uses Haskell Integer / quotRem. These are
-- test oracles, not Phil's implementation helpers. Small widths bound enumeration.
controls :: [(String, Check)]
controls =
  [ ("C01", forM_ [1..6] $ \w -> forM_ (uOps) $ \(op,tag,f) ->
      forM_ [(a,b) | a <- uValues w, b <- uValues w] $ \(a,b) -> do
        let r=f a b
            expected = if uFits w r
              then CU.CheckedUIntArithmeticSucceeded (CU.CheckedUIntArithmeticSuccess (ScalarUIntLiteral w r) (uProp tag w a b r))
              else CU.CheckedUIntArithmeticNegative (if op == U.UIntSubtract then CU.checkedUIntUnderflowFailure else CU.checkedUIntOverflowFailure)
        same (Right expected) (CU.checkCheckedUIntArithmetic op w (ScalarUIntLiteral w a) (ScalarUIntLiteral w b)))
  , ("C02", do
      same (Left (CU.CheckedUIntArithmeticInvalidWidth 0)) (CU.checkCheckedUIntArithmetic U.UIntAdd 0 (ScalarUIntLiteral 0 0) (ScalarUIntLiteral 0 0))
      same (Left (CU.CheckedUIntArithmeticOperandTypeMismatch CU.CheckedUIntLeftOperand (ScalarBoolLiteral True) 8))
        (CU.checkCheckedUIntArithmetic U.UIntAdd 8 (ScalarBoolLiteral True) (ScalarUIntLiteral 8 0))
      same (Left (CU.CheckedUIntArithmeticOperandTypeMismatch CU.CheckedUIntRightOperand (ScalarUIntLiteral 16 0) 8))
        (CU.checkCheckedUIntArithmetic U.UIntAdd 8 (ScalarUIntLiteral 8 1) (ScalarUIntLiteral 16 0))
      same (Left (CU.CheckedUIntArithmeticOperandOutOfRange CU.CheckedUIntLeftOperand (ScalarUIntLiteral 8 256)))
        (CU.checkCheckedUIntArithmetic U.UIntMultiply 8 (ScalarUIntLiteral 8 256) (ScalarUIntLiteral 8 0)))
  , ("C03", forM_ [1..4] $ \w -> forM_ uOps $ \(op,_,f) ->
      forM_ [(a,b) | a <- uValues w,b <- uValues w] $ \(a,b) -> do
        let r=f a b; supplied=if uFits w r then r else 0
            expected=if uFits w r then Right (U.PlainUIntArithmeticEstablished (ScalarUIntLiteral w r))
              else Left (U.UIntArithmeticKnownResultOutOfRange op w a b r)
        same expected (U.checkPlainUIntArithmetic emptyCheckState op w (RefUInt w a) (RefUInt w b) (RefUInt w supplied) uSite))
  , ("C04", do
      same (Left (U.UIntArithmeticKnownResultMismatch U.UIntSubtract 8 7 2 5 4))
        (U.checkPlainUIntArithmetic emptyCheckState U.UIntSubtract 8 (RefUInt 8 7) (RefUInt 8 2) (RefUInt 8 4) uSite)
      same (Left (U.UIntArithmeticSortError (InvalidUIntLiteral 8 256)))
        (U.checkPlainUIntArithmetic emptyCheckState U.UIntMultiply 8 (RefUInt 8 256) (RefUInt 8 0) ur uSite))
  , ("C05", do
      let prop=Atom "phil.uint.add.exact.v1" [RefNat 8,RefToNat ux,RefToNat uy,RefToNat ur]
      same (Right (U.PlainUIntArithmeticRequiresProof (expectedOb "n2.uint" prop)))
        (U.checkPlainUIntArithmetic emptyCheckState U.UIntAdd 8 ux uy ur uSite))
  , ("C06", forM_ [1..4] $ \w -> forM_ sOps $ \(op,_,f) ->
      forM_ [(a,b) | a <- iValues w,b <- iValues w] $ \(a,b) -> do
        let r=f a b; supplied=if iFits w r then r else 0
            expected=if iFits w r then Right (S.PlainSIntArithmeticEstablished (sl w r))
              else Left (S.SIntArithmeticKnownResultOutOfRange op w a b r)
        same expected (S.checkPlainSIntArithmetic emptyCheckState op (S.SIntType w) (sk w a) (sk w b) (sk w supplied) sSite))
  , ("C07", do
      same (Left (S.SIntArithmeticKnownTermOutOfRange (sl 8 128)))
        (S.checkPlainSIntArithmetic emptyCheckState S.SIntMultiply (S.SIntType 8) (sk 8 128) (sk 8 0) sr sSite)
      same (Left (S.SIntArithmeticKnownResultMismatch S.SIntSubtract 8 7 2 5 4))
        (S.checkPlainSIntArithmetic emptyCheckState S.SIntSubtract (S.SIntType 8) (sk 8 7) (sk 8 2) (sk 8 4) sSite)
      let bad=S.SIntSymbolic (S.SIntType 8) " "
      same (Left (S.SIntArithmeticEmptySymbolicIdentity bad))
        (S.checkPlainSIntArithmetic emptyCheckState S.SIntAdd (S.SIntType 8) bad sy sr sSite))
  , ("C08", do
      let bias n=RefOpaque SortNat ("phil.sint.bias.v1:I8:" <> n)
          prop=Atom "phil.sint.sub.exact.v1" [RefNat 8,bias "x",bias "y",bias "r"]
      same (Right (S.PlainSIntArithmeticRequiresProof (expectedOb "n2.sint" prop)))
        (S.checkPlainSIntArithmetic emptyCheckState S.SIntSubtract (S.SIntType 8) sx sy sr sSite))
  , ("C09", forM_ [(a,b) | a <- [-63..63], b <- [-63..63], b/=0] $ \(a,b) -> do
      let (q,r)=D.signedQuotientRemainder a b
      same (quotRem a b) (q,r)
      truth "quotient/remainder reconstruction" (a==q*b+r)
      truth "remainder magnitude" (abs r < abs b)
      truth "remainder sign follows dividend" (r==0 || signum r==signum a))
  , ("C10", forM_ [1..6] $ \w -> forM_ dOps $ \(op,tag) ->
      forM_ [(a,b) | a<-iValues w,b<-iValues w] $ \(a,b) -> do
        let (q,r)=if b==0 then (0,0) else quotRem a b
            z=if op==D.IntegerQuotient then q else r
            expected=if b==0 then D.CheckedDivisionNegative D.checkedIntegerDivideByZeroFailure
              else if not (iFits w z) then D.CheckedDivisionNegative D.checkedSignedDivisionOverflowFailure
              else D.CheckedDivisionSucceeded (sl w z) (iProp tag w a b z)
        same (Right expected) (D.checkCheckedSIntDivision op (S.SIntType w) (sl w a) (sl w b)))
  , ("C11", forM_ [1..6] $ \w -> forM_ dOps $ \(op,tag) ->
      forM_ [(a,b) | a<-uValues w,b<-uValues w] $ \(a,b) -> do
        let z=if b==0 then 0 else if op==D.IntegerQuotient then a `quot` b else a `rem` b
            expected=if b==0 then D.CheckedDivisionNegative D.checkedIntegerDivideByZeroFailure
              else D.CheckedDivisionSucceeded (ScalarUIntLiteral w z) (uProp tag w a b z)
        same (Right expected) (D.checkCheckedUIntDivision op w (ScalarUIntLiteral w a) (ScalarUIntLiteral w b)))
  , ("C12", do
      same (Left (D.CheckedSIntDivisionOperandOutOfRange (sl 8 128)))
        (D.checkCheckedSIntDivision D.IntegerQuotient (S.SIntType 8) (sl 8 128) (sl 8 0))
      same (Left (D.CheckedUIntDivisionOperandOutOfRange (ScalarUIntLiteral 8 256)))
        (D.checkCheckedUIntDivision D.IntegerQuotient 8 (ScalarUIntLiteral 8 256) (ScalarUIntLiteral 8 0))
      same (Left (D.CheckedUIntDivisionOperandTypeMismatch (ScalarUIntLiteral 16 1) 8))
        (D.checkCheckedUIntDivision D.IntegerQuotient 8 (ScalarUIntLiteral 8 7) (ScalarUIntLiteral 16 1)))
  , ("C13", do
      same (Left (D.SIntDivisionKnownResultOutOfRange D.IntegerQuotient 8 (-128) (-1) 128))
        (D.checkPlainSIntDivision emptyCheckState D.IntegerQuotient (S.SIntType 8) (sk 8 (-128)) (sk 8 (-1)) (sk 8 0) dSite)
      same (Right (D.PlainSIntDivisionEstablished (sl 8 0)))
        (D.checkPlainSIntDivision emptyCheckState D.IntegerRemainder (S.SIntType 8) (sk 8 (-128)) (sk 8 (-1)) (sk 8 0) dSite)
      same (Right (D.PlainSIntDivisionEstablished (sl 8 (-1))))
        (D.checkPlainSIntDivision emptyCheckState D.IntegerRemainder (S.SIntType 8) (sk 8 (-7)) (sk 8 2) (sk 8 (-1)) dSite))
  , ("C14", do
      same (Left (D.UIntDivisionKnownZeroDivisor 8 7))
        (D.checkPlainUIntDivision emptyCheckState D.IntegerQuotient 8 (RefUInt 8 7) (RefUInt 8 0) ur dSite)
      same (Left (D.UIntDivisionKnownResultMismatch D.IntegerQuotient 8 7 2 3 2))
        (D.checkPlainUIntDivision emptyCheckState D.IntegerQuotient 8 (RefUInt 8 7) (RefUInt 8 2) (RefUInt 8 2) dSite))
  , ("C15", do
      let p=Atom "phil.uint.quot.exact.v1" [RefNat 8,RefToNat ux,RefToNat uy,RefToNat ur]
      same (Right (D.PlainUIntDivisionRequiresProof (expectedOb "n2.div" p)))
        (D.checkPlainUIntDivision emptyCheckState D.IntegerQuotient 8 ux uy ur dSite))
  , ("C16", forM_ [1..8] $ \w -> forM_ [H.IntegerShiftLeft,H.IntegerShiftRight] $ \op ->
      forM_ [(n,k) | n<-uValues w,k<-[-1..toInteger w]] $ \(n,k) -> do
        let valid=0<=k && k<toInteger w
            z=if not valid then 0 else if op==H.IntegerShiftLeft then n*2^k else n `quot` (2^k)
            expected=if not valid then Left (H.IntegerShiftCountOutOfRange w k)
              else if not (uFits w z) then Left (H.IntegerShiftUIntLeftResultOutOfRange w z) else Right z
        same expected (H.applyUIntShift op w n k))
  , ("C17", forM_ [1..8] $ \w -> forM_ [H.IntegerShiftLeft,H.IntegerShiftRight] $ \op ->
      forM_ [(n,k) | n<-iValues w,k<-[-1..toInteger w]] $ \(n,k) -> do
        let valid=0<=k && k<toInteger w
            -- Exact Rational floor avoids copying production's Integer div expression.
            z=if not valid then 0 else if op==H.IntegerShiftLeft then n*2^k else floor (fromInteger n / fromInteger (2^k) :: Rational)
            expected=if not valid then Left (H.IntegerShiftCountOutOfRange w k)
              else if not (iFits w z) then Left (H.IntegerShiftSIntLeftResultOutOfRange (S.SIntType w) z) else Right z
        same expected (H.applySIntShift op (S.SIntType w) n k))
  , ("C18", do
      same (Left (H.IntegerShiftInvalidWidth 0)) (H.applyUIntShift H.IntegerShiftRight 0 999 (-1))
      same (Left (H.IntegerShiftCountOutOfRange 8 8)) (H.applyUIntShift H.IntegerShiftRight 8 256 8)
      same (Left (H.IntegerShiftUIntOperandOutOfRange 8 256)) (H.applyUIntShift H.IntegerShiftRight 8 256 1)
      same (Left (H.IntegerShiftSIntOperandOutOfRange (S.SIntType 8) 128)) (H.applySIntShift H.IntegerShiftRight (S.SIntType 8) 128 1))
  , ("C19", forM_ [1..8] $ \sw -> forM_ [1..8] $ \tw -> do
      let sources=map (N.NumericUIntValue sw) (uValues sw) ++ map (nv sw) (iValues sw)
      forM_ sources $ \v -> forM_ [N.NumericUIntType tw,N.NumericSIntType (S.SIntType tw)] $ \target -> do
        let n=magnitude v
            fits=case target of N.NumericUIntType _ -> uFits tw n; _ -> iFits tw n
            value=case target of N.NumericUIntType _ -> N.NumericUIntValue tw n; _ -> nv tw n
            expected=if fits then Right (N.NumericConversionResult value N.NumericConversionExact) else Left (N.NumericConversionOutOfRange target v)
        same expected (N.convertNumericValue target v))
  , ("C20", do
      let bad=N.NumericUIntValue 8 256; badTarget=N.NumericUIntType 0
      same (Left (N.NumericConversionInvalidTarget badTarget)) (N.convertNumericValue badTarget bad)
      same (Left (N.NumericConversionInvalidSource bad)) (N.convertNumericValue (N.NumericUIntType 16) bad)
      same (Left (N.NumericConversionInvalidSource (nv 8 128))) (N.convertNumericValue (N.NumericSIntType (S.SIntType 16)) (nv 8 128)))
  , ("C21", forM_ [N.NumericUIntType 0,N.NumericUIntType 8,N.NumericSIntType (S.SIntType 8),N.NumericUIntType 16] $ \target ->
      forM_ [N.NumericUIntValue 8 7,N.NumericUIntValue 16 256,N.NumericUIntValue 8 256,nv 8 (-1)] $ \source ->
        let expected=either N.CheckedNumericConversionFailed N.CheckedNumericConversionSucceeded (N.convertNumericValue target source)
        in same expected (N.checkedConvertNumericValue target source))
  , ("C22", do
      let n=2^(127::Int)+123
      same (Right (N.NumericConversionResult (N.NumericUIntValue 256 n) N.NumericConversionExact))
        (N.convertNumericValue (N.NumericUIntType 256) (N.NumericUIntValue 128 n))
      same (Left (N.NumericConversionOutOfRange (N.NumericSIntType (S.SIntType 128)) (N.NumericUIntValue 128 n)))
        (N.convertNumericValue (N.NumericSIntType (S.SIntType 128)) (N.NumericUIntValue 128 n)))
  , ("C23", do
      checkEval "x / d" [("x",nv 8 (-3)),("d",nv 8 2)] (Right (nv 8 (-1)))
      checkEval "x % d" [("x",nv 8 (-3)),("d",nv 8 2)] (Right (nv 8 (-1)))
      checkEval "x >> k" [("x",nv 8 (-3)),("k",N.NumericUIntValue 8 1)] (Right (nv 8 (-2))))
  , ("C24", do
      let env=[("a",N.NumericUIntValue 8 255),("b",N.NumericUIntValue 8 1)]
      checkEval "convert (a + b) to U16" env (Left (E.GrammarV1NumericArithmeticOutOfRange (N.NumericUIntType 8) 256))
      checkEval "(convert a to U16) + (convert b to U16)" env (Right (N.NumericUIntValue 16 256)))
  , ("C25", do
      let env=[("a",N.NumericUIntValue 8 7),("b",N.NumericUIntValue 16 2)]
      checkEval "a + b" env (Left (E.GrammarV1NumericMixedDomainRequiresConversion (N.NumericUIntType 8) (N.NumericUIntType 16)))
      checkEval "(convert a to U16) + b" env (Right (N.NumericUIntValue 16 9)))
  , ("C26", do
      checkEval "x >> k" [("x",nv 8 (-5)),("k",N.NumericUIntValue 16 1)] (Right (nv 8 (-3)))
      checkEval "x >> k" [("x",N.NumericUIntValue 8 255),("k",nv 16 (-1))]
        (Left (E.GrammarV1NumericShiftError (H.IntegerShiftCountOutOfRange 8 (-1)))))
  , ("C27", do
      checkEval "a - b" [("a",N.NumericUIntValue 8 0),("b",N.NumericUIntValue 8 1)]
        (Left (E.GrammarV1NumericArithmeticOutOfRange (N.NumericUIntType 8) (-1)))
      checkEval "a / b" [("a",nv 8 (-128)),("b",nv 8 (-1))]
        (Left (E.GrammarV1NumericArithmeticOutOfRange (N.NumericSIntType (S.SIntType 8)) 128))
      checkEval "a % b" [("a",nv 8 (-128)),("b",nv 8 (-1))] (Right (nv 8 0))
      checkEval "a / b" [("a",N.NumericUIntValue 8 7),("b",N.NumericUIntValue 8 0)]
        (Left (E.GrammarV1NumericDivideByZero (N.NumericUIntType 8) D.IntegerQuotient)))
  , ("C28", forM_ ["accept x as U16","transport x to U16 using e","7"] $ \text -> do
      expr <- parseExpr text
      same (Left (E.GrammarV1NumericUnsupportedExpression expr))
        (E.evaluateGrammarV1NumericExpression (numEnv [("x",N.NumericUIntValue 8 7)]) expr))
  , ("C29", do
      expr <- parseExpr "-128 + 0"
      same (Right (S.PlainSIntArithmeticEstablished (sl 8 (-128)),emptyCheckState))
        (SA.checkGrammarV1PlainSIntArithmetic emptyCheckState (GrammarV1UnsignedType "I8") Map.empty expr (sk 8 (-128)) sSite))
  , ("C30", do
      uexpr <- parseExpr "7 / 2"
      same (Right (D.PlainUIntDivisionEstablished (ScalarUIntLiteral 8 3),emptyCheckState))
        (SD.checkGrammarV1PlainUIntDivision emptyCheckState (GrammarV1UnsignedType "U8") Map.empty uexpr (RefUInt 8 3) dSite)
      iexpr <- parseExpr "-7 % 2"
      same (Right (D.PlainSIntDivisionEstablished (sl 8 (-1)),emptyCheckState))
        (SD.checkGrammarV1PlainSIntDivision emptyCheckState (GrammarV1UnsignedType "I8") Map.empty iexpr (sk 8 (-1)) dSite))
  , ("C31", do
      expr <- parseExpr "x + y"
      let env=Map.fromList [(ref "x",sx),(ref "y",sy)]
          prop=S.plainSIntArithmeticProposition S.SIntAdd (S.SIntType 8) sx sy sr
          obligation=expectedOb "n2.sint" prop
          kept=expectedOb "preexisting" Truth
          start=emptyCheckState {residualObligations=Map.singleton (obligationId kept) kept}
      (decision,next) <- expectRight (SA.checkGrammarV1PlainSIntArithmetic start (GrammarV1UnsignedType "I8") env expr sr sSite)
      same (S.PlainSIntArithmeticRequiresProof obligation) decision
      same (resourceContext start) (resourceContext next)
      same (Map.fromList [(obligationId kept,kept),(obligationId obligation,obligation)]) (residualObligations next)
      same (Right (decision,next)) (SA.checkGrammarV1PlainSIntArithmetic next (GrammarV1UnsignedType "I8") env expr sr sSite)
      let bad=obligation {obligationScope="other.scope"}
          conflict=start {residualObligations=Map.singleton (obligationId bad) bad}
      same (Left (SA.GrammarV1PlainSIntObligationError (ConflictingObligationId bad obligation)))
        (SA.checkGrammarV1PlainSIntArithmetic conflict (GrammarV1UnsignedType "I8") env expr sr sSite))
  , ("C32", do
      expr <- parseExpr "x / y"
      same (Right (D.CheckedDivisionSucceeded (sl 8 (-3)) (iProp "quot" 8 (-7) 2 (-3))))
        (SD.checkGrammarV1CheckedSIntDivision (GrammarV1UnsignedType "I8") expr (sl 8 (-7)) (sl 8 2))
      same (Right (D.CheckedDivisionNegative D.checkedIntegerDivideByZeroFailure))
        (SD.checkGrammarV1CheckedUIntDivision (GrammarV1UnsignedType "U8") expr (ScalarUIntLiteral 8 7) (ScalarUIntLiteral 8 0)))
  , ("C33", do
      checkEval "a + b << k" [("a",N.NumericUIntValue 8 1),("b",N.NumericUIntValue 8 1),("k",N.NumericUIntValue 8 2)] (Right (N.NumericUIntValue 8 8))
      checkEval "x << b >> c" [("x",N.NumericUIntValue 8 4),("b",N.NumericUIntValue 8 1),("c",N.NumericUIntValue 8 2)] (Right (N.NumericUIntValue 8 2)))
  , ("C34", do
      expr <- parseExpr "(-x) + z"
      let env=Map.fromList [(ref "x",sk 8 (-128)),(ref "z",sk 8 0)]
      same (Left (SA.GrammarV1PlainSIntNegationOutOfRange (sl 8 128)))
        (SA.checkGrammarV1PlainSIntArithmetic emptyCheckState (GrammarV1UnsignedType "I8") env expr (sk 8 0) sSite))
  , ("C35", do
      same (Set.singleton CU.checkedUIntOverflowFailure) (CU.checkedUIntArithmeticFailures U.UIntAdd)
      same (Set.singleton CU.checkedUIntUnderflowFailure) (CU.checkedUIntArithmeticFailures U.UIntSubtract)
      same (Set.singleton CU.checkedUIntOverflowFailure) (CU.checkedUIntArithmeticFailures U.UIntMultiply)
      same (Set.fromList [D.checkedIntegerDivideByZeroFailure,D.checkedSignedDivisionOverflowFailure]) (D.checkedSIntDivisionFailures D.IntegerQuotient)
      same (Set.singleton D.checkedIntegerDivideByZeroFailure) (D.checkedSIntDivisionFailures D.IntegerRemainder))
  , ("C36", do
      expr <- parseExpr "left + right"
      same (Left (E.GrammarV1NumericUnknownReference (ref "left"))) (E.evaluateGrammarV1NumericExpression Map.empty expr)
      same (Left (E.GrammarV1NumericUnknownReference (ref "right")))
        (E.evaluateGrammarV1NumericExpression (numEnv [("left",N.NumericUIntValue 8 1)]) expr))
  , ("C37", do
      expr <- parseExpr "7 - 2"
      same (Right (U.PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 5),emptyCheckState))
        (UA.checkGrammarV1PlainUIntArithmetic emptyCheckState (GrammarV1UnsignedType "U8") Map.empty expr (RefUInt 8 5) uSite)
      divExpr <- parseExpr "7 / 2"
      same (Left (UA.GrammarV1PlainUIntOperatorNotPlainArithmetic GrammarV1Divide))
        (UA.checkGrammarV1PlainUIntArithmetic emptyCheckState (GrammarV1UnsignedType "U8") Map.empty divExpr (RefUInt 8 3) uSite))
  , ("C38", do
      expr <- parseExpr "x + y"
      let env=Map.fromList [(ref "x",ux),(ref "y",uy)]
          prop=Atom "phil.uint.add.exact.v1" [RefNat 8,RefToNat ux,RefToNat uy,RefToNat ur]
          obligation=expectedOb "n2.uint" prop
      (decision,next) <- expectRight (UA.checkGrammarV1PlainUIntArithmetic emptyCheckState (GrammarV1UnsignedType "U8") env expr ur uSite)
      same (U.PlainUIntArithmeticRequiresProof obligation) decision
      same (Map.singleton (obligationId obligation) obligation) (residualObligations next)
      same (resourceContext emptyCheckState) (resourceContext next))
  ]

-- Observations describe a supplied-input boundary, NOT acceptance defects.
observations :: [(String, Check)]
observations =
  [ ("O01", do
      first <- parseExpr "x / y"
      second <- parseExpr "unboundA / unboundB"
      let run expr=SD.checkGrammarV1CheckedUIntDivision (GrammarV1UnsignedType "U8") expr (ScalarUIntLiteral 8 7) (ScalarUIntLiteral 8 2)
      same (Right (D.CheckedDivisionSucceeded (ScalarUIntLiteral 8 3) (uProp "quot" 8 7 2 3))) (run first)
      same (run first) (run second))
  , ("O02", do
      let prop=D.plainUIntDivisionProposition D.IntegerQuotient 8 ux (RefUInt 8 0) ur
      same (Right (D.PlainUIntDivisionRequiresProof (expectedOb "n2.div" prop)))
        (D.checkPlainUIntDivision emptyCheckState D.IntegerQuotient 8 ux (RefUInt 8 0) ur dSite)
      let prop2=S.plainSIntArithmeticProposition S.SIntAdd (S.SIntType 8) (sk 8 127) (sk 8 1) sr
      same (Right (S.PlainSIntArithmeticRequiresProof (expectedOb "n2.sint" prop2)))
        (S.checkPlainSIntArithmetic emptyCheckState S.SIntAdd (S.SIntType 8) (sk 8 127) (sk 8 1) sr sSite))
  ]

magnitude :: N.NumericValue -> Integer
magnitude (N.NumericUIntValue _ n) = n
magnitude (N.NumericSIntValue literal) = S.sIntLiteralValue literal
magnitude (N.NumericFloatValue _) = error "N2 integer-only test inventory contains float"

ref :: Text -> GrammarV1StaticReference
ref name = GrammarV1StaticReference (GrammarV1QualifiedName [name]) []
numEnv :: [(Text,N.NumericValue)] -> E.GrammarV1NumericEnvironment
numEnv = Map.fromList . map (\(name,value) -> (ref name,value))
parseExpr :: Text -> Either Failure GrammarV1Expression
parseExpr text = do
  parsed <- setup (parseGrammarV1StructuralSource "audit-n2.phil" ("component N2 { return " <> text <> "; }"))
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ReturnStatement expression)] -> Right (locatedValue expression)
          other -> Left (Setup ("expected one return, got " ++ show other))
      other -> Left (Setup ("expected component, got " ++ show other))
    other -> Left (Setup ("expected one declaration, got " ++ show other))
checkEval :: Text -> [(Text,N.NumericValue)] -> Either E.GrammarV1NumericEvaluationError N.NumericValue -> Check
checkEval text bindings expected = do
  expr <- parseExpr text
  same expected (E.evaluateGrammarV1NumericExpression (numEnv bindings) expr)
