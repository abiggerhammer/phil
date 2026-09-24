{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.NumericConversion
import Phil.Core.Refinement (RefinementError (..))
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.SIntArithmetic (SIntLiteral (..), SIntType (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), ValueError (..), checkValue)
import qualified Phil.Surface.GrammarV1.BinderScope as B
import qualified Phil.Surface.GrammarV1.LexicalReferenceScope as L
import qualified Phil.Surface.GrammarV1.NumericConversion as N
import qualified Phil.Surface.GrammarV1.Parser as G
import qualified Phil.Surface.GrammarV1.RuntimeScalar as R
import qualified Phil.Surface.GrammarV1.SemanticBindingState as S
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

-- Boundary adapters in THIS FILE are audit-owned, not a discovered compiler
-- pipeline. Declaration lineage and contextual numeric type are explicit
-- premises. The actual parser, literal admission, binder allocation, lexical
-- resolution, occurrence rewrite, numeric evaluator and Core value checker are
-- called directly. Their positive returned records are never fabricated.
-- Installing a checked literal under its derived key and projecting an actual
-- UInt result into VUInt are the two narrow audit joins being measured.

data SourceCase = SourceCase
  { sourceName :: Located Text.Text
  , sourceLiteral :: Located G.GrammarV1Expression
  , sourceReturn :: Located G.GrammarV1Expression
  }

data Prepared = Prepared
  { preparedSource :: SourceCase
  , preparedBinder :: B.GrammarV1ResolvedBinder
  , preparedExpression :: Located G.GrammarV1Expression
  , preparedEnvironment :: N.GrammarV1NumericEnvironment
  , preparedValue :: NumericValue
  }

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False problem = Left problem
need :: String -> Maybe a -> Either String a
need problem = maybe (Left problem) Right

parseCase :: Text.Text -> Either String SourceCase
parseCase source = do
  parsed <- right $ G.parseGrammarV1StructuralSource "numeric-adapter-audit.phil" source
  case G.grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (G.grammarV1Declaration top) of
      G.GrammarV1ComponentDeclaration component ->
        case G.grammarV1BlockStatements (locatedValue (G.grammarV1ComponentBody component)) of
          [ Located _ (G.GrammarV1LetStatement (Located _ (G.GrammarV1IdentifierPattern name)) literal)
            , Located _ (G.GrammarV1ReturnStatement expression) ] ->
              Right (SourceCase name literal expression)
          other -> Left ("expected one let and one return: " <> show other)
      other -> Left ("expected component: " <> show other)
    other -> Left ("expected exactly one component: " <> show other)

key :: B.GrammarV1ResolvedBinder -> G.GrammarV1StaticReference
key binder = case B.grammarV1ResolvedBinderCoreName binder of
  Name name -> G.GrammarV1StaticReference (G.GrammarV1QualifiedName [name]) []

admit :: G.GrammarV1Type -> G.GrammarV1Expression -> Either String NumericValue
admit context expression = case context of
  G.GrammarV1UnsignedType spelling | Text.isPrefixOf "I" spelling ->
    NumericSIntValue <$> right (R.grammarV1ContextualSIntLiteral context expression)
  _ -> do
    literal <- right $ R.grammarV1ContextualUIntLiteral context expression
    case literal of
      ScalarUIntLiteral width value -> Right (NumericUIntValue width value)
      other -> Left ("not a UInt literal: " <> show other)

prepare :: DeclarationKey -> G.GrammarV1Type -> Text.Text -> Either String Prepared
prepare root context source = do
  parsed <- parseCase source
  actual <- admit context (locatedValue (sourceLiteral parsed))
  (binder,scope) <- right $ B.grammarV1BindLocal B.GrammarV1LetPatternBinder
    (sourceName parsed) (B.grammarV1RootLexicalScope root)
  references <- need "unsupported lexical expression" $
    L.grammarV1CheckedExpressionReferences Set.empty scope (sourceReturn parsed)
  resolved <- right references
  ensure (not (null resolved)) "fixture must contain an actual lexical use"
  ensure (all ((== binder) . L.grammarV1CheckedLexicalReferenceBinder) resolved)
    "lexical reference selected a different binder"
  expression <- need "unsupported semantic occurrence rewrite" $
    S.grammarV1RewriteExpressionReferences resolved (sourceReturn parsed)
  -- Explicit audit environment assembly, using only the authentic derived key
  -- and authentic admitted width/value. No display-name fallback is introduced.
  let environment = Map.singleton (key binder) actual
  pure (Prepared parsed binder expression environment actual)

evaluate :: Prepared -> Either String NumericValue
evaluate p = right $ N.evaluateGrammarV1NumericExpression
  (preparedEnvironment p) (locatedValue (preparedExpression p))

rootA, rootB :: DeclarationKey
rootA = DeclarationKey "audit.numeric.root-A"
rootB = DeclarationKey "audit.numeric.root-B"
u8, u16, i8 :: G.GrammarV1Type
u8 = G.GrammarV1UnsignedType "U8"
u16 = G.GrammarV1UnsignedType "U16"
i8 = G.GrammarV1UnsignedType "I8"

seven :: Either String Prepared
seven = prepare rootA u8 "component C { let n = 7; return convert n to U16; }"

sourceToResult :: Either String ()
sourceToResult = do
  p <- seven
  ensure (preparedValue p == NumericUIntValue 8 7) "literal admission changed source"
  actual <- evaluate p
  ensure (actual == NumericUIntValue 16 7) "explicit conversion changed value/domain"
  converted <- right $ convertNumericValue (NumericUIntType 16) (preparedValue p)
  ensure (numericConversionValue converted == actual
    && numericConversionPrecision converted == NumericConversionExact)
    "conversion metadata differs from the actual evaluator result"

alphaRename :: Either String ()
alphaRename = do
  first <- seven
  second <- prepare rootA u8 "component C { let m = 7; return convert m to U16; }"
  ensure (key (preparedBinder first) == key (preparedBinder second))
    "display rename changed fixed-lineage ordinal identity"
  ensure (sourceName (preparedSource first) /= sourceName (preparedSource second))
    "fixture did not actually change the source spelling"
  a <- evaluate first
  b <- evaluate second
  ensure (a == NumericUIntValue 16 7 && a == b) "renaming changed the actual numeric result"

differentRoot :: Either String ()
differentRoot = do
  first <- prepare rootA u8 "component C { let n = 7; return n; }"
  second <- prepare rootB u8 "component C { let n = 7; return n; }"
  let otherKey = key (preparedBinder second)
  ensure (key (preparedBinder first) /= otherKey) "different declaration roots collapsed"
  ensure (N.evaluateGrammarV1NumericExpression (preparedEnvironment first)
    (locatedValue (preparedExpression second)) == Left (N.GrammarV1NumericUnknownReference otherKey))
    "another declaration's leaf was used by name"

siblingScopes :: Either String ()
siblingScopes = do
  parsed <- parseCase "component C { let n = 7; return n; }"
  let root = B.grammarV1RootLexicalScope rootA
  (first,inside) <- right $ B.grammarV1BindLocal B.GrammarV1LetPatternBinder
    (sourceName parsed) (B.grammarV1EnterLexicalScope root)
  outside <- right $ B.grammarV1LeaveLexicalScope inside
  ensure (B.grammarV1ResolveLocal (sourceName parsed) outside ==
    Left (B.GrammarV1BinderNotInScope (sourceName parsed))) "left scope remained active"
  (second,_) <- right $ B.grammarV1BindLocal B.GrammarV1LetPatternBinder
    (sourceName parsed) (B.grammarV1EnterLexicalScope outside)
  ensure (key first /= key second) "sibling scope reused old numeric identity"
  actual <- admit u8 (locatedValue (sourceLiteral parsed))
  ensure (N.evaluateGrammarV1NumericExpression (Map.singleton (key first) actual)
    (G.GrammarV1NameExpression (key second) []) ==
      Left (N.GrammarV1NumericUnknownReference (key second))) "old sibling supplied new leaf"

repeatedUse :: Either String ()
repeatedUse = do
  p <- prepare rootA u8 "component C { let n = 7; return n + n; }"
  case locatedValue (preparedExpression p) of
    G.GrammarV1BinaryExpression (Located _ (G.GrammarV1NameExpression left [])) _
      (Located _ (G.GrammarV1NameExpression rightKey [])) ->
        ensure (left == key (preparedBinder p) && rightKey == left)
          "repeated lexical occurrences did not use exact binder key"
    other -> Left ("unexpected rewritten expression: " <> show other)
  actual <- evaluate p
  ensure (actual == NumericUIntValue 8 14) "actual repeated-operand result changed"

noDisplayFallback :: Either String ()
noDisplayFallback = do
  p <- prepare rootA u8 "component C { let n = 7; return n; }"
  case locatedValue (sourceReturn (preparedSource p)) of
    expression@(G.GrammarV1NameExpression displayKey []) ->
      ensure (N.evaluateGrammarV1NumericExpression (preparedEnvironment p) expression ==
        Left (N.GrammarV1NumericUnknownReference displayKey))
        "numeric lookup silently fell back to display spelling"
    other -> Left ("unexpected original expression: " <> show other)

literalBoundary :: Either String ()
literalBoundary = do
  p <- seven
  let expression = locatedValue (sourceLiteral (preparedSource p))
  ensure (N.evaluateGrammarV1NumericExpression Map.empty expression ==
    Left (N.GrammarV1NumericUnsupportedExpression expression))
    "untyped literal entered the already-identified-leaf evaluator"
  ensure (preparedValue p == NumericUIntValue 8 7) "contextual literal control failed"

signedMinimum :: Either String ()
signedMinimum = do
  p <- prepare rootA i8 "component C { let n = -128; return convert n to I16; }"
  ensure (preparedValue p == NumericSIntValue (SIntLiteral (SIntType 8) (-128)))
    "source sign was not applied before signed literal admission"
  actual <- evaluate p
  ensure (actual == NumericSIntValue (SIntLiteral (SIntType 16) (-128)))
    "signed widening lost domain or mathematical sign"

fittingNarrow :: Either String ()
fittingNarrow = do
  p <- prepare rootA u16 "component C { let n = 255; return convert n to U8; }"
  actual <- evaluate p
  ensure (actual == NumericUIntValue 8 255) "valid narrowing did not preserve value"

rejectNarrow :: Either String ()
rejectNarrow = do
  p <- prepare rootA u16 "component C { let n = 300; return convert n to U8; }"
  ensure (N.evaluateGrammarV1NumericExpression (preparedEnvironment p)
    (locatedValue (preparedExpression p)) ==
      Left (N.GrammarV1NumericConversionError
        (NumericConversionOutOfRange (NumericUIntType 8) (preparedValue p))))
    "out-of-range conversion did not reject at the numeric consumer"

actualCoreValue :: Either String (Value, ValueResult)
actualCoreValue = do
  p <- seven
  numeric <- evaluate p
  case numeric of
    NumericUIntValue width value -> do
      let core = VUInt width value -- explicit audit-owned exact constructor join
      checked <- right $ checkValue core (TyUInt width) emptyCheckState
      ensure (valueResultType checked == TyUInt 16
        && valueResultTerm checked == Just (RefUInt 16 7)
        && valueResultState checked == emptyCheckState)
        "actual result-to-Core width/value/state correspondence failed"
      pure (core,checked)
    other -> Left ("unsupported audit numeric-to-Core domain: " <> show other)

refinementConsumer :: Either String ()
refinementConsumer = do
  (core,_) <- actualCoreValue
  let binder = Name "result"
      predicate = Equal (RefVar binder) (RefUInt 16 7)
      expected = TyRefined binder (TyUInt 16) predicate
  result <- right $ checkValue core expected emptyCheckState
  ensure (valueResultType result == expected && valueResultTerm result == Just (RefUInt 16 7))
    "refinement did not bind the actual returned numeric subject"
  ensure (checkValue (VUInt 16 8) expected emptyCheckState ==
    Left (ValueRefinementError (StaticallyFalse (Equal (RefUInt 16 8) (RefUInt 16 7)))))
    "same-typed different value inherited result evidence"

indexConsumer :: Bool -> Either String ()
indexConsumer shouldFit = do
  p <- if shouldFit then seven else
    prepare rootA u8 "component C { let n = 8; return convert n to U16; }"
  numeric <- evaluate p
  term <- case numeric of
    NumericUIntValue width value -> do
      checked <- right $ checkValue (VUInt width value) (TyUInt width) emptyCheckState
      need "actual Core literal had no term" (valueResultTerm checked)
    other -> Left ("wrong index domain: " <> show other)
  let buffer = Name "buffer"
      actualTy = TyBytes (RefNat 7)
      expectedTy = TyBytes (RefToNat term)
  resources <- right $ insertBinding Linear buffer actualTy (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = resources }
  if shouldFit then do
    result <- right $ checkValue (VVar buffer) expectedTy before
    ensure (valueResultType result == expectedTy && valueResultTerm result == Just (RefVar buffer))
      "dependent index used a different numeric result"
    ensure (resourceContext (valueResultState result) == resourceContext emptyCheckState)
      "linear indexed value was not consumed exactly once"
  else ensure (checkValue (VVar buffer) expectedTy before ==
      Left (ExplicitTransportRequired actualTy expectedTy))
    "another numeric result was silently substituted as the dependent length"

rejectNegativeUInt :: Either String ()
rejectNegativeUInt = do
  p <- prepare rootA i8 "component C { let n = -1; return convert n to U8; }"
  ensure (N.evaluateGrammarV1NumericExpression (preparedEnvironment p)
    (locatedValue (preparedExpression p)) ==
      Left (N.GrammarV1NumericConversionError
        (NumericConversionOutOfRange (NumericUIntType 8) (preparedValue p))))
    "negative signed value was reinterpreted as unsigned or a natural index"

forwardReference :: Either String ()
forwardReference = do
  parsed <- parseCase "component C { let n = 7; return m; }"
  (_,scope) <- right $ B.grammarV1BindLocal B.GrammarV1LetPatternBinder
    (sourceName parsed) (B.grammarV1RootLexicalScope rootA)
  let expression = sourceReturn parsed
      occurrence = Located (locatedSpan expression) "m"
  ensure (L.grammarV1CheckedExpressionReferences (Set.singleton "m") scope expression ==
    Just (Left (L.GrammarV1LexicalReferenceForwardReference occurrence)))
    "pending lexical declaration was treated as an admitted numeric leaf"

main :: IO ()
main = do
  outcomes <- sequence
    [ test "C01" "actual source literal, binder and explicit result correspondence" sourceToResult
    , test "C02" "alpha rename preserves fixed-lineage numeric identity" alphaRename
    , test "C03" "same-spelled other declaration cannot supply the leaf" differentRoot
    , test "C04" "sibling scope preserves fresh binder identity" siblingScopes
    , test "C05" "repeated source occurrences use the exact selected leaf" repeatedUse
    , test "C06" "unrewritten display names do not alias semantic keys" noDisplayFallback
    , test "C07" "literal admission is separate from numeric leaf evaluation" literalBoundary
    , test "C08" "signed minimum survives actual literal admission and widening" signedMinimum
    , test "C09" "fitting narrowing preserves the actual magnitude" fittingNarrow
    , test "C10" "out-of-range narrowing rejects at the exact consumer" rejectNarrow
    , test "C11" "actual UInt result reaches Core with its exact term and type" (actualCoreValue >> pure ())
    , test "C12" "dependent refinement cannot transfer to a different value" refinementConsumer
    , test "C13" "actual returned number becomes the dependent length" (indexConsumer True)
    , test "C14" "different returned length requires explicit transport" (indexConsumer False)
    , test "C15" "negative signed result is not an unsigned index" rejectNegativeUInt
    , test "C16" "pending lexical reference cannot enter the numeric environment" forwardReference
    ]
  putStrLn "COMPLETE numeric_adapter_groups=16"
  unless (and outcomes) exitFailure

test :: String -> String -> Either String () -> IO Bool
test label description result = case result of
  Right () -> putStrLn ("PASS " <> label <> " " <> description) >> pure True
  Left detail -> putStrLn ("FAIL " <> label <> " " <> description <> " -- " <> detail) >> pure False
