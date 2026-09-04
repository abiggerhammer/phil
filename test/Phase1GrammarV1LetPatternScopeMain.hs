{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Value (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  , GrammarV1CheckedLetScopeTrace (..)
  , GrammarV1LetPatternScopeError (..)
  , grammarV1CheckedClosureLetPatternScope
  , grammarV1CheckedFunctionLetPatternScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-009 recursive let patterns allocate binders in exact source preorder"
        recursiveLetPatternSourceOrder
    , test "SURF-009 let initializers cannot see binders introduced by that let"
        letInitializerCannotSeeNewBinder
    , test "SURF-009 duplicate binders inside one recursive pattern reject"
        duplicateRecursivePatternRejects
    , test "SURF-009 let binders cannot shadow active function parameters"
        letCannotShadowParameter
    , test "SURF-009 closure lets resolve outer, closure, and let-local binders exactly"
        closureLetScopeComposes
    , test "SURF-009 tuple-pattern alpha renaming preserves semantic binder identity"
        tuplePatternAlphaRenamingPreservesIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

recursiveLetPatternSourceOrder :: Either String ()
recursiveLetPatternSourceOrder = do
  functionDecl <- onlyFunction "let-pattern-preorder" $ Text.unlines
    [ "fn pattern_scope(seed : U8) -> U8 satisfies C {"
    , "  let (left, Pair { short, nested = (right, tail) }) = seed;"
    , "  left;"
    , "  short;"
    , "  right;"
    , "  return tail;"
    , "}"
    ]
  trace <- checkedFunctionLetTrace (DeclarationKey "decl.PatternScope") functionDecl
  parameterBinder <- exactlyOne
    "function parameter binder"
    (grammarV1CheckedLetParameterBinders trace)
  case grammarV1CheckedLetScopeSteps trace of
    GrammarV1CheckedLetBindingStep _ initializer binders : occurrenceSteps -> do
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder initializer)
          == grammarV1ResolvedBinderKey parameterBinder)
        "let initializer was not resolved in the pre-binding parameter scope"
      assert
        (grammarV1CheckedLocalValueCore initializer
          == VVar (grammarV1ResolvedBinderCoreName parameterBinder))
        "let initializer did not use the exact parameter Core name"
      assert
        (map grammarV1ResolvedBinderDisplayName binders
          == ["left", "short", "right", "tail"])
        "recursive pattern binder preorder or record-field shorthand was wrong"
      assert
        (map occurrenceBinderName occurrenceSteps
          == map grammarV1ResolvedBinderDisplayName binders)
        "subsequent statements did not resolve recursive pattern binders in order"
      assert
        (map occurrenceCoreValue occurrenceSteps
          == map (VVar . grammarV1ResolvedBinderCoreName) binders)
        "subsequent statements did not use exact generated let-binder Core names"
    other -> Left ("expected one let step followed by four occurrences, got " <> show other)

letInitializerCannotSeeNewBinder :: Either String ()
letInitializerCannotSeeNewBinder = do
  functionDecl <- onlyFunction "let-pattern-self" $ Text.unlines
    [ "fn self_scope(seed : U8) -> U8 satisfies C {"
    , "  let alias = alias;"
    , "  return alias;"
    , "}"
    ]
  case grammarV1CheckedFunctionLetPatternScope
      (DeclarationKey "decl.SelfScope") functionDecl of
    Nothing -> Right ()
    other -> Left
      ("let initializer incorrectly saw its own future binder: " <> show other)

duplicateRecursivePatternRejects :: Either String ()
duplicateRecursivePatternRejects = do
  functionDecl <- onlyFunction "let-pattern-duplicate" $ Text.unlines
    [ "fn duplicate_pattern(seed : U8) -> U8 satisfies C {"
    , "  let (item, item) = seed;"
    , "  return item;"
    , "}"
    ]
  case grammarV1CheckedFunctionLetPatternScope
      (DeclarationKey "decl.DuplicatePattern") functionDecl of
    Just (Left (GrammarV1LetPatternBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "item")
          "duplicate recursive-pattern diagnostic lost source spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "item")
          "duplicate recursive-pattern diagnostic lost first binder"
    other -> Left ("expected recursive-pattern duplicate rejection, got " <> show other)

letCannotShadowParameter :: Either String ()
letCannotShadowParameter = do
  functionDecl <- onlyFunction "let-pattern-shadow" $ Text.unlines
    [ "fn shadow_scope(seed : U8) -> U8 satisfies C {"
    , "  let seed = seed;"
    , "  return seed;"
    , "}"
    ]
  case grammarV1CheckedFunctionLetPatternScope
      (DeclarationKey "decl.ShadowScope") functionDecl of
    Just (Left (GrammarV1LetPatternBinderError
      (GrammarV1DuplicateBinder duplicate previous))) -> do
        assert (locatedValue duplicate == "seed")
          "parameter-shadow rejection lost let spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "seed")
          "parameter-shadow rejection lost active parameter binder"
    other -> Left ("expected active parameter-name rejection, got " <> show other)

closureLetScopeComposes :: Either String ()
closureLetScopeComposes = do
  outerFunction <- onlyFunction "let-pattern-outer" $ Text.unlines
    [ "fn outer_scope(seed : U8) -> U8 satisfies C {"
    , "  return seed;"
    , "}"
    ]
  closure <- onlyClosure "let-pattern-closure" $ Text.unlines
    [ "component Holder() {"
    , "  closure (item : U8) satisfies C {"
    , "    let (copy, nested) = seed;"
    , "    item;"
    , "    copy;"
    , "    return nested;"
    , "  };"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.ClosureLet"
  (outerBinders, outerScope) <- mapLeft show
    (grammarV1FunctionParameterScope declarationKey outerFunction)
  outerBinder <- exactlyOne "outer parameter binder" outerBinders
  trace <- case grammarV1CheckedClosureLetPatternScope outerScope closure of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked closure let scope, got " <> show other)
  closureBinder <- exactlyOne
    "closure parameter binder"
    (grammarV1CheckedLetParameterBinders trace)
  case grammarV1CheckedLetScopeSteps trace of
    GrammarV1CheckedLetBindingStep _ initializer letBinders : occurrenceSteps -> do
      assert
        (grammarV1ResolvedBinderKey (grammarV1CheckedLocalValueBinder initializer)
          == grammarV1ResolvedBinderKey outerBinder)
        "closure let initializer did not resolve enclosing parameter"
      assert
        (map grammarV1ResolvedBinderDisplayName letBinders == ["copy", "nested"])
        "closure tuple-pattern binders were not allocated in source order"
      let expectedBinders = closureBinder : letBinders
      assert
        (map occurrenceBinderKey occurrenceSteps
          == map grammarV1ResolvedBinderKey expectedBinders)
        "closure body did not resolve closure-local then let-local binders exactly"
      assert
        (map occurrenceCoreValue occurrenceSteps
          == map (VVar . grammarV1ResolvedBinderCoreName) expectedBinders)
        "closure body did not preserve exact Core names"
    other -> Left ("expected closure let plus three local occurrences, got " <> show other)

tuplePatternAlphaRenamingPreservesIdentity :: Either String ()
tuplePatternAlphaRenamingPreservesIdentity = do
  original <- onlyFunction "let-pattern-alpha-original" $ Text.unlines
    [ "fn tuple_alpha(seed : U8) -> U8 satisfies C {"
    , "  let (left, (middle, right)) = seed;"
    , "  return right;"
    , "}"
    ]
  renamed <- onlyFunction "let-pattern-alpha-renamed" $ Text.unlines
    [ "fn tuple_alpha(source : U8) -> U8 satisfies C {"
    , "    let (a, (b, c)) = source;"
    , "    return c;"
    , "}"
    ]
  let declarationKey = DeclarationKey "decl.TupleAlpha"
  originalTrace <- checkedFunctionLetTrace declarationKey original
  renamedTrace <- checkedFunctionLetTrace declarationKey renamed
  originalBinders <- firstLetBinders originalTrace
  renamedBinders <- firstLetBinders renamedTrace
  assert
    (map grammarV1ResolvedBinderKey originalBinders
      == map grammarV1ResolvedBinderKey renamedBinders)
    "alpha-renaming tuple-pattern binders changed semantic identity"
  assert
    (map grammarV1ResolvedBinderCoreName originalBinders
      == map grammarV1ResolvedBinderCoreName renamedBinders)
    "alpha-renaming tuple-pattern binders changed Core identity"
  assert
    (map grammarV1ResolvedBinderDisplayName originalBinders
      == ["left", "middle", "right"])
    "original tuple-pattern spellings were not retained diagnostically"
  assert
    (map grammarV1ResolvedBinderDisplayName renamedBinders == ["a", "b", "c"])
    "renamed tuple-pattern spellings were not retained diagnostically"

checkedFunctionLetTrace
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Either String GrammarV1CheckedLetScopeTrace
checkedFunctionLetTrace declarationKey functionDecl =
  case grammarV1CheckedFunctionLetPatternScope declarationKey functionDecl of
    Just (Right trace) -> Right trace
    other -> Left ("expected checked function let scope, got " <> show other)

firstLetBinders
  :: GrammarV1CheckedLetScopeTrace
  -> Either String [GrammarV1ResolvedBinder]
firstLetBinders trace = case grammarV1CheckedLetScopeSteps trace of
  GrammarV1CheckedLetBindingStep _ _ binders : _ -> Right binders
  other -> Left ("expected leading let-binding step, got " <> show other)

occurrenceBinderKey :: GrammarV1CheckedLetScopeStep -> GrammarV1BinderKey
occurrenceBinderKey step =
  grammarV1ResolvedBinderKey (occurrenceBinder step)

occurrenceBinderName :: GrammarV1CheckedLetScopeStep -> Text.Text
occurrenceBinderName = grammarV1ResolvedBinderDisplayName . occurrenceBinder

occurrenceCoreValue :: GrammarV1CheckedLetScopeStep -> Value
occurrenceCoreValue step = case step of
  GrammarV1CheckedLetOccurrenceStep _ occurrence ->
    grammarV1CheckedLocalValueCore occurrence
  other -> error ("expected occurrence step, got " <> show other)

occurrenceBinder :: GrammarV1CheckedLetScopeStep -> GrammarV1ResolvedBinder
occurrenceBinder step = case step of
  GrammarV1CheckedLetOccurrenceStep _ occurrence ->
    grammarV1CheckedLocalValueBinder occurrence
  other -> error ("expected occurrence step, got " <> show other)

onlyFunction :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
onlyFunction label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1FunctionDeclaration functionDecl -> Right functionDecl
      other -> Left ("expected function declaration, got " <> show other)
    declarations -> Left
      ("expected one function declaration, got " <> show (length declarations))

onlyClosure :: Text.Text -> Text.Text -> Either String GrammarV1Closure
onlyClosure label source = do
  sourceFile <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ComponentDeclaration componentDecl ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody componentDecl)) of
          [Located _ (GrammarV1ExpressionStatement expression)] ->
            closureFromExpression expression
          statements -> Left
            ("expected one closure-bearing statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left
      ("expected one component declaration, got " <> show (length declarations))

closureFromExpression
  :: Located GrammarV1Expression
  -> Either String GrammarV1Closure
closureFromExpression (Located _ expression) = case expression of
  GrammarV1ClosureExpression closure -> Right closure
  other -> Left ("expected closure expression, got " <> show other)

exactlyOne :: String -> [a] -> Either String a
exactlyOne _ [value] = Right value
exactlyOne label values = Left
  ("expected exactly one " <> label <> ", got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
