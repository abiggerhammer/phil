{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.NumericConversion (NumericValue (..))
import Phil.Core.Refinement (RefinementError (..))
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Core.Value (ValueError (..), ValueResult (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  , grammarV1RootLexicalScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError (..)
  , grammarV1CheckedExpressionReferences
  )
import Phil.Surface.GrammarV1.NumericConversion
  ( GrammarV1NumericAdmissionError (..)
  , checkGrammarV1UIntNumericResult
  , evaluateAndCheckGrammarV1UIntNumericExpression
  , evaluateGrammarV1CheckedNumericExpression
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.RuntimeScalar
  ( grammarV1ContextualUIntLiteral
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

span0 :: SourceSpan
span0 =
  let point = SourcePoint "phase1-audit-numeric-admission" 1 1 0
  in SourceSpan point point

bindLocal
  :: Text
  -> GrammarV1LexicalScope
  -> Either String (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindLocal display scope =
  leftShow (grammarV1BindLocal
    GrammarV1FunctionParameterBinder
    (Located span0 display)
    scope)

parseReturn :: Text -> Either String (Located GrammarV1Expression)
parseReturn expressionText = do
  parsed <- leftShow $ parseGrammarV1StructuralSource
    "phase1-audit-numeric-admission.phil"
    ("component NumericAdmission { return " <> expressionText <> "; }")
  case grammarV1TopLevelDecls parsed of
    [Located _ top] ->
      case locatedValue (grammarV1Declaration top) of
        GrammarV1ComponentDeclaration component ->
          case grammarV1BlockStatements
              (locatedValue (grammarV1ComponentBody component)) of
            [Located _ (GrammarV1ReturnStatement expression)] -> Right expression
            other -> Left ("setup: expected one return statement, got " <> show other)
        other -> Left ("setup: expected component declaration, got " <> show other)
    other -> Left ("setup: expected one declaration, got " <> show other)

checked
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either String [GrammarV1CheckedLexicalReference]
checked scope expression =
  case grammarV1CheckedExpressionReferences Set.empty scope expression of
    Just (Right references) -> Right references
    Just (Left problem) -> Left ("lexical reference check failed: " <> show problem)
    Nothing -> Left "expression is outside the checked numeric lexical fragment"

uintLeaf :: Int -> Text -> Either String NumericValue
uintLeaf width source = do
  expression <- parseReturn source
  literal <- leftShow $ grammarV1ContextualUIntLiteral
    (GrammarV1UnsignedType ("U" <> Text.pack (show width)))
    (locatedValue expression)
  case literal of
    ScalarUIntLiteral actualWidth magnitude ->
      Right (NumericUIntValue actualWidth magnitude)
    other -> Left ("setup: expected UInt literal, got " <> show other)

singleBinder
  :: Text
  -> Text
  -> Either String (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
singleBinder root display =
  bindLocal display (grammarV1RootLexicalScope (DeclarationKey root))

semanticValue
  :: GrammarV1ResolvedBinder
  -> NumericValue
  -> Map.Map Name NumericValue
semanticValue binder value =
  Map.singleton (grammarV1ResolvedBinderCoreName binder) value

caseExactSemanticAdmission :: Either String ()
caseExactSemanticAdmission = do
  (binder, scope) <- singleBinder "numeric.root" "value"
  expression <- parseReturn "value"
  references <- checked scope expression
  value <- uintLeaf 8 "7"
  actual <- leftShow $ evaluateGrammarV1CheckedNumericExpression
    (semanticValue binder value) references expression
  same value actual

caseRepeatedOccurrence :: Either String ()
caseRepeatedOccurrence = do
  (binder, scope) <- singleBinder "numeric.repeated" "x"
  expression <- parseReturn "x + x"
  references <- checked scope expression
  value <- uintLeaf 8 "7"
  actual <- leftShow $ evaluateGrammarV1CheckedNumericExpression
    (semanticValue binder value) references expression
  same (NumericUIntValue 8 14) actual
  assert (length references == 2) "repeated source occurrences were not both checked"

caseAlphaRenameStable :: Either String ()
caseAlphaRenameStable = do
  (before, beforeScope) <- singleBinder "numeric.alpha" "before"
  (after, afterScope) <- singleBinder "numeric.alpha" "renamed"
  assert
    (grammarV1ResolvedBinderCoreName before == grammarV1ResolvedBinderCoreName after)
    "alpha rename changed semantic binder identity"
  value <- uintLeaf 8 "11"
  beforeExpression <- parseReturn "before"
  afterExpression <- parseReturn "renamed"
  beforeReferences <- checked beforeScope beforeExpression
  afterReferences <- checked afterScope afterExpression
  let admitted = semanticValue before value
  leftShow (evaluateGrammarV1CheckedNumericExpression admitted beforeReferences beforeExpression)
    >>= same value
  leftShow (evaluateGrammarV1CheckedNumericExpression admitted afterReferences afterExpression)
    >>= same value

caseDeclarationRootsSeparate :: Either String ()
caseDeclarationRootsSeparate = do
  (leftBinder, _) <- singleBinder "numeric.root.left" "x"
  (rightBinder, rightScope) <- singleBinder "numeric.root.right" "x"
  assert
    (grammarV1ResolvedBinderCoreName leftBinder /= grammarV1ResolvedBinderCoreName rightBinder)
    "different declaration roots collapsed semantic binder identity"
  expression <- parseReturn "x"
  references <- checked rightScope expression
  value <- uintLeaf 8 "7"
  case evaluateGrammarV1CheckedNumericExpression
      (semanticValue leftBinder value) references expression of
    Left (GrammarV1NumericBindingValueMissing name)
      | name == grammarV1ResolvedBinderCoreName rightBinder -> Right ()
    other -> Left ("different declaration root reused numeric admission: " <> show other)

caseSiblingScopesSeparate :: Either String ()
caseSiblingScopesSeparate = do
  let root = grammarV1RootLexicalScope (DeclarationKey "numeric.siblings")
  (firstBinder, firstScope) <- bindLocal "x" (grammarV1EnterLexicalScope root)
  parent <- leftShow (grammarV1LeaveLexicalScope firstScope)
  (secondBinder, secondScope) <- bindLocal "x" (grammarV1EnterLexicalScope parent)
  assert
    (grammarV1ResolvedBinderCoreName firstBinder /= grammarV1ResolvedBinderCoreName secondBinder)
    "sibling lexical binders reused semantic identity"
  expression <- parseReturn "x"
  firstReferences <- checked firstScope expression
  secondReferences <- checked secondScope expression
  seven <- uintLeaf 8 "7"
  eight <- uintLeaf 8 "8"
  let admitted = Map.fromList
        [ (grammarV1ResolvedBinderCoreName firstBinder, seven)
        , (grammarV1ResolvedBinderCoreName secondBinder, eight)
        ]
  leftShow (evaluateGrammarV1CheckedNumericExpression admitted firstReferences expression)
    >>= same seven
  leftShow (evaluateGrammarV1CheckedNumericExpression admitted secondReferences expression)
    >>= same eight

caseDisplaySpellingNotAuthority :: Either String ()
caseDisplaySpellingNotAuthority = do
  (binder, scope) <- singleBinder "numeric.display" "value"
  expression <- parseReturn "value"
  references <- checked scope expression
  seven <- uintLeaf 8 "7"
  case evaluateGrammarV1CheckedNumericExpression
      (Map.singleton (Name "value") seven) references expression of
    Left (GrammarV1NumericBindingValueMissing name)
      | name == grammarV1ResolvedBinderCoreName binder -> Right ()
    other -> Left ("display spelling became numeric authority: " <> show other)

caseActualUIntResultReachesCore :: Either String ()
caseActualUIntResultReachesCore = do
  let root = grammarV1RootLexicalScope (DeclarationKey "numeric.result")
  (leftBinder, scope1) <- bindLocal "left" root
  (rightBinder, scope2) <- bindLocal "right" scope1
  expression <- parseReturn "convert (left - right) to U16"
  references <- checked scope2 expression
  nine <- uintLeaf 8 "9"
  two <- uintLeaf 8 "2"
  let admitted = Map.fromList
        [ (grammarV1ResolvedBinderCoreName leftBinder, nine)
        , (grammarV1ResolvedBinderCoreName rightBinder, two)
        ]
      subject = Name "subject"
      target = TyRefined subject (TyUInt 16)
        (Equal (RefVar subject) (RefUInt 16 7))
  result <- leftShow $ evaluateAndCheckGrammarV1UIntNumericExpression
    admitted references expression target emptyCheckState
  same target (valueResultType result)
  same (Just (RefUInt 16 7)) (valueResultTerm result)

caseWrongResultCannotBorrowSubject :: Either String ()
caseWrongResultCannotBorrowSubject = do
  let actual = NumericUIntValue 16 7
      subject = Name "subject"
      wrong = TyRefined subject (TyUInt 16)
        (Equal (RefVar subject) (RefUInt 16 8))
  case checkGrammarV1UIntNumericResult actual wrong emptyCheckState of
    Left (GrammarV1NumericResultCheckFailed
      (ValueRefinementError (StaticallyFalse proposition)))
      | proposition == Equal (RefUInt 16 7) (RefUInt 16 8) -> Right ()
    other -> Left ("actual numeric result acquired a different subject: " <> show other)

caseForwardReferenceStillRejects :: Either String ()
caseForwardReferenceStillRejects = do
  let scope = grammarV1RootLexicalScope (DeclarationKey "numeric.forward")
  expression <- parseReturn "later"
  case grammarV1CheckedExpressionReferences
      (Set.singleton "later") scope expression of
    Just (Left (GrammarV1LexicalReferenceForwardReference source))
      | locatedValue source == "later" -> Right ()
    other -> Left ("forward reference escaped lexical admission: " <> show other)

cases :: [(String, Either String ())]
cases =
  [ ("A01 exact semantic admission", caseExactSemanticAdmission)
  , ("A02 repeated occurrences", caseRepeatedOccurrence)
  , ("A03 alpha rename", caseAlphaRenameStable)
  , ("A04 declaration roots", caseDeclarationRootsSeparate)
  , ("A05 sibling scopes", caseSiblingScopesSeparate)
  , ("A06 display spelling", caseDisplaySpellingNotAuthority)
  , ("A07 actual UInt result", caseActualUIntResultReachesCore)
  , ("A08 wrong result subject", caseWrongResultCannotBorrowSubject)
  , ("A09 forward reference", caseForwardReferenceStillRejects)
  ]

main :: IO ()
main = do
  outcomes <- mapM run cases
  unless (and outcomes) exitFailure
  where
    run (label, outcome) =
      case outcome of
        Right () -> putStrLn ("PASS " <> label) >> pure True
        Left problem -> putStrLn ("FAIL " <> label <> " -- " <> problem) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

same :: (Eq a, Show a) => a -> a -> Either String ()
same expected actual =
  assert (expected == actual)
    ("expected " <> show expected <> "; got " <> show actual)

leftShow :: Show e => Either e a -> Either String a
leftShow = either (Left . show) Right
