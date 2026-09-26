{-# LANGUAGE OverloadedStrings #-}
-- Independent first-party numeric interface review. PREPARED, NOT EXECUTED.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import qualified Phil.Core.Discharge as D
import qualified Phil.Core.NumericConversion as N
import Phil.Core.Refinement (RefinementError (..), ResidualSpec (..))
import Phil.Core.Scalar (ScalarLiteral (..))
import qualified Phil.Core.SIntArithmetic as S
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import qualified Phil.Core.UIntArithmetic as U
import Phil.Core.Value (ValueError (..), ValueResult (..), checkValue, checkValueWithResidual)
import qualified Phil.Surface.GrammarV1.NumericConversion as E
import qualified Phil.Surface.GrammarV1.RuntimeScalar as R
import qualified Phil.Surface.GrammarV1.UIntArithmetic as UA
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1ComponentDecl (..), GrammarV1Declaration (..)
  , GrammarV1Expression (..), GrammarV1SourceFile (..), GrammarV1Statement (..)
  , GrammarV1StaticReference, GrammarV1TopLevelDecl (..), GrammarV1Type (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

-- Registry construction and NumericValue -> Value conversion below are AUDIT
-- ADAPTERS, not a newly discovered production compiler path. Every numeric leaf
-- comes from the real contextual literal checker; the converted payload is taken
-- from the real evaluator/converter result. A parsed reference is still not a
-- resolved declaration/binder identity. No invalid numeric environment is used.
right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False problem = Left problem
same :: (Eq a, Show a) => a -> a -> Either String ()
same expected actual = ensure (expected == actual)
  ("expected " <> show expected <> "; got " <> show actual)

parseExpr :: Text -> Either String GrammarV1Expression
parseExpr text = do
  parsed <- right $ parseGrammarV1StructuralSource "audit-numeric-adapters.phil"
    ("component NumericAdapter { return " <> text <> "; }")
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ReturnStatement expression)] -> Right (locatedValue expression)
          other -> Left ("setup: expected one return: " <> show other)
      other -> Left ("setup: expected component: " <> show other)
    other -> Left ("setup: expected one declaration: " <> show other)

reference :: Text -> Either String GrammarV1StaticReference
reference text = do
  expression <- parseExpr text
  case expression of
    GrammarV1NameExpression name [] -> Right name
    other -> Left ("setup: expected a complete static reference: " <> show other)

uintLeaf :: Int -> Text -> Either String N.NumericValue
uintLeaf width text = do
  expression <- parseExpr text
  checked <- right $ R.grammarV1ContextualUIntLiteral
    (GrammarV1UnsignedType ("U" <> Text.pack (show width))) expression
  case checked of
    ScalarUIntLiteral actualWidth magnitude -> Right (N.NumericUIntValue actualWidth magnitude)
    other -> Left ("setup: expected UInt literal: " <> show other)

sintLeaf :: Int -> Text -> Either String N.NumericValue
sintLeaf width text = do
  expression <- parseExpr text
  N.NumericSIntValue <$> right (R.grammarV1ContextualSIntLiteral
    (GrammarV1UnsignedType ("I" <> Text.pack (show width))) expression)

registry :: [(Text, N.NumericValue)] -> Either String E.GrammarV1NumericEnvironment
registry entries = Map.fromList <$> mapM attach entries
  where attach (name,value) = do key <- reference name; pure (key,value)

runExpression :: Text -> E.GrammarV1NumericEnvironment -> Either String N.NumericValue
runExpression text environment = do
  expression <- parseExpr text
  right $ E.evaluateGrammarV1NumericExpression environment expression

actualSeven :: Either String N.NumericValue
actualSeven = do
  nine <- uintLeaf 8 "9"
  two <- uintLeaf 8 "2"
  environment <- registry [("left",nine),("right",two)]
  result <- runExpression "convert (left - right) to U16" environment
  same (N.NumericUIntValue 16 7) result
  pure result

coreLiteral :: N.NumericValue -> Either String Value
coreLiteral value = case value of
  N.NumericUIntValue width magnitude -> Right (VUInt width magnitude)
  other -> Left ("audit adapter intentionally supports UInt only: " <> show other)

refined :: Int -> Integer -> Ty
refined width magnitude = TyRefined (Name "subject") (TyUInt width)
  (Equal (RefVar (Name "subject")) (RefUInt width magnitude))

checkedSeven :: Either String ValueResult
checkedSeven = do
  actual <- actualSeven
  value <- coreLiteral actual
  result <- right $ checkValue value (refined 16 7) emptyCheckState
  same (Just (RefUInt 16 7)) (valueResultTerm result)
  same (refined 16 7) (valueResultType result)
  same Map.empty (residualObligations (valueResultState result))
  pure result

bind :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
bind mode name ty state = do
  context <- right $ insertBinding mode name ty (resourceContext state)
  pure state { resourceContext = context }

controls :: [(String, String, Either String ())]
controls =
  [ ("C01","contextual UInt admission supplies exact width and magnitude",do
      value <- uintLeaf 8 "255"
      same (N.NumericUIntValue 8 255) value
      environment <- registry [("original",value)]
      result <- runExpression "original" environment
      same value result)
  , ("C02","out-of-range source literal rejects before registry installation",do
      expression <- parseExpr "256"
      same (Left (R.GrammarV1RuntimeUIntLiteralOutOfRange 8 256))
        (R.grammarV1ContextualUIntLiteral (GrammarV1UnsignedType "U8") expression))
  , ("C03","signed minimum survives contextual sign admission",do
      value <- sintLeaf 8 "-128"
      same (N.NumericSIntValue (S.SIntLiteral (S.SIntType 8) (-128))) value)
  , ("C04","complete qualified reference keys are distinct",do
      seven <- uintLeaf 8 "7"
      eight <- uintLeaf 8 "8"
      keyA <- reference "alpha.x"
      keyB <- reference "beta.x"
      ensure (keyA /= keyB) "qualified source references collapsed"
      environment <- registry [("alpha.x",seven),("beta.x",eight)]
      runExpression "alpha.x" environment >>= same seven
      runExpression "beta.x" environment >>= same eight
      expression <- parseExpr "x"
      unqualified <- reference "x"
      same (Left (E.GrammarV1NumericUnknownReference unqualified))
        (E.evaluateGrammarV1NumericExpression environment expression))
  , ("C05","explicit width conversion precedes mixed-domain arithmetic",do
      seven <- uintLeaf 8 "7"
      two <- uintLeaf 16 "2"
      environment <- registry [("x",seven),("y",two)]
      expression <- parseExpr "x + y"
      same (Left (E.GrammarV1NumericMixedDomainRequiresConversion
        (N.NumericUIntType 8) (N.NumericUIntType 16)))
        (E.evaluateGrammarV1NumericExpression environment expression)
      runExpression "(convert x to U16) + y" environment >>= same (N.NumericUIntValue 16 9))
  , ("C06","signed/unsigned arithmetic preserves explicit converted domains",do
      negative <- sintLeaf 8 "-7"
      positive <- uintLeaf 8 "2"
      environment <- registry [("negative",negative),("positive",positive)]
      runExpression "(convert negative to I16) + (convert positive to I16)" environment
        >>= same (N.NumericSIntValue (S.SIntLiteral (S.SIntType 16) (-5))))
  , ("C07","bare literal is outside the bounded evaluator, not contextual admission",do
      expression <- parseExpr "7"
      same (Left (E.GrammarV1NumericUnsupportedExpression expression))
        (E.evaluateGrammarV1NumericExpression Map.empty expression)
      uintLeaf 8 "7" >>= same (N.NumericUIntValue 8 7))
  , ("C08","actual evaluated/converted payload reaches exact Core refinement",checkedSeven >> pure ())
  , ("C09","actual returned payload cannot satisfy a different closed value",do
      actual <- actualSeven >>= coreLiteral
      same (Left (ValueRefinementError (StaticallyFalse
        (Equal (RefUInt 16 7) (RefUInt 16 8)))))
        (checkValue actual (refined 16 8) emptyCheckState))
  , ("C10","Core checking does not silently widen an unconverted value",do
      actual <- uintLeaf 8 "7" >>= coreLiteral
      same (Left (ValueTypeMismatch (TyUInt 8) (TyUInt 16)))
        (checkValue actual (TyUInt 16) emptyCheckState))
  , ("C11","valid wide source outside the target range remains a conversion error",do
      actual <- uintLeaf 16 "256"
      same (Left (N.NumericConversionOutOfRange (N.NumericUIntType 8) actual))
        (N.convertNumericValue (N.NumericUIntType 8) actual))
  , ("C12","an actual result is not evidence about an unrelated same-typed variable",do
      number <- checkedSeven
      term <- maybe (Left "setup: missing actual literal term") Right (valueResultTerm number)
      let name = Name "result"
          goal = Equal (RefVar name) term
          spec = ResidualSpec (ObligationId "numeric-adapter.unrelated") "numeric-adapter" "scope" "before-use"
      state <- bind Unrestricted name (TyUInt 16) (valueResultState number)
      result <- right $ checkValueWithResidual spec (VVar name) (refined 16 7) state
      obligation <- maybe (Left "setup: actual residual missing") Right $
        Map.lookup (residualObligationId spec) (residualObligations (valueResultState result))
      same goal (obligationProposition obligation)
      same (Left (D.UnresolvedObligation (obligationId obligation) goal))
        (D.resolveObligation emptyStaticContext (valueResultState result) D.emptyDischargePolicy obligation))
  , ("C13","a new binding can carry the actual checked result's returned refinement",do
      number <- checkedSeven
      let name = Name "result"
      state <- bind Unrestricted name (valueResultType number) (valueResultState number)
      result <- right $ checkValue (VVar name) (refined 16 7) state
      same (Just (RefVar name)) (valueResultTerm result)
      same Map.empty (residualObligations (valueResultState result))
      same (resourceContext state) (resourceContext (valueResultState result)))
  , ("C14","dependent byte index uses the returned number and consumes only its owner",do
      number <- checkedSeven
      term <- maybe (Left "setup: missing result term") Right (valueResultTerm number)
      let name = Name "bytes"
          target = TyBytes (RefToNat term)
      state <- bind Linear name (TyBytes (RefNat 7)) emptyCheckState
      result <- right $ checkValue (VVar name) target state
      same target (valueResultType result)
      let context = resourceContext (valueResultState result)
      ensure (all (Map.notMember name) [unrestrictedBindings context,affineBindings context,linearBindings context])
        "the byte owner was not consumed"
      other <- bind Linear name (TyBytes (RefNat 8)) emptyCheckState
      same (Left (ExplicitTransportRequired (TyBytes (RefNat 8)) target))
        (checkValue (VVar name) target other))
  , ("C15","the existing arithmetic bridge checks the actual evaluator result",do
      nine <- uintLeaf 8 "9"
      two <- uintLeaf 8 "2"
      environment <- registry [("left",nine),("right",two)]
      expression <- parseExpr "left - right"
      value <- right $ E.evaluateGrammarV1NumericExpression environment expression
      (width,magnitude) <- case value of
        N.NumericUIntValue w n -> Right (w,n)
        other -> Left ("setup: expected UInt: " <> show other)
      leftKey <- reference "left"
      rightKey <- reference "right"
      leftTerm <- case nine of
        N.NumericUIntValue w n -> Right (RefUInt w n)
        other -> Left ("setup: wrong actual left domain: " <> show other)
      rightTerm <- case two of
        N.NumericUIntValue w n -> Right (RefUInt w n)
        other -> Left ("setup: wrong actual right domain: " <> show other)
      let terms = Map.fromList [(leftKey,leftTerm),(rightKey,rightTerm)]
          site = U.PlainUIntArithmeticSite (ObligationId "numeric-adapter.arithmetic") "numeric-adapter" "scope" "before-use"
      same (Right (U.PlainUIntArithmeticEstablished (ScalarUIntLiteral 8 7),emptyCheckState))
        (UA.checkGrammarV1PlainUIntArithmetic emptyCheckState (GrammarV1UnsignedType "U8")
          terms expression (RefUInt width magnitude) site)
      same (Left (UA.GrammarV1PlainUIntCoreError (U.UIntArithmeticKnownResultMismatch U.UIntSubtract 8 9 2 7 8)))
        (UA.checkGrammarV1PlainUIntArithmetic emptyCheckState (GrammarV1UnsignedType "U8")
          terms expression (RefUInt 8 8) site))
  , ("C16","negative signed value requires a valid explicit unsigned conversion",do
      actual <- sintLeaf 8 "-1"
      same (Left (N.NumericConversionOutOfRange (N.NumericUIntType 16) actual))
        (N.convertNumericValue (N.NumericUIntType 16) actual))
  ]

main :: IO ()
main = do
  outcomes <- mapM run controls
  putStrLn "COMPLETE numeric_adapter_groups=16"
  unless (and outcomes) exitFailure
  where
    run (key,label,outcome) = case outcome of
      Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
      Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
