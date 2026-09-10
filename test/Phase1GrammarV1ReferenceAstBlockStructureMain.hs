{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockStructure
  ( grammarV1ProductionBlockCore
  , grammarV1ProductionJoinClauseCore
  , grammarV1ProductionMatchArmCore
  , grammarV1ProductionStateBindingCore
  , grammarV1ReferenceBlockCore
  , grammarV1ReferenceJoinClauseCore
  , grammarV1ReferenceMatchArmCore
  , grammarV1ReferenceStateBindingCore
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceParseSourceTokens
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ checkBlock
            "patterns-and-statements"
            (Text.unlines
              [ "component C {"
              , "  let (x, y) = pair;"
              , "  let Pair{left = x, right,} = pair;"
              , "  return x;"
              , "}"
              ])
        , checkMatchArms
            "match-arm-binders"
            (Text.unlines
              [ "component C {"
              , "  match value {"
              , "    Some(x) => return x;"
              , "    Pair{left as l, right,} => { return l; }"
              , "  };"
              , "}"
              ])
        , checkJoin
            "join-state-and-invariant"
            "component C { if true join state (x: U8, y: Bytes[4]) invariant true { return unit; }; }"
        , checkStateBindings
            "loop-state-bindings"
            "component C { loop state (x: U8 = 0, y = 1) invariant true { break; }; }"
        , checkEmptyBlock
        , checkMalformedTree
        ]
      failures = [detail | Left detail <- checks]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn "PASS: certified Grammar-v1 block/match substrate agrees with production AST"
    else exitFailure

checkBlock :: String -> Text -> Either String ()
checkBlock label source = do
  (tree, production) <- parseBoth label source
  referenceBlockTree <- oneNamed "block" tree
  reference <- mapLeft show (grammarV1ReferenceBlockCore referenceBlockTree)
  component <- onlyComponent production
  let productionValue =
        grammarV1ProductionBlockCore (locatedValue (grammarV1ComponentBody component))
  equal label reference productionValue

checkMatchArms :: String -> Text -> Either String ()
checkMatchArms label source = do
  (tree, production) <- parseBoth label source
  let armTrees = allNamed "match_arm" tree
  reference <- traverse (mapLeft show . grammarV1ReferenceMatchArmCore) armTrees
  expression <- onlyComponentExpression production
  productionArms <- case expression of
    GrammarV1MatchExpression _ _ arms ->
      Right (map (grammarV1ProductionMatchArmCore . locatedValue) arms)
    other -> Left (label <> " -- expected match expression, got " <> show other)
  equal label reference productionArms

checkJoin :: String -> Text -> Either String ()
checkJoin label source = do
  (tree, production) <- parseBoth label source
  joinTree <- oneNamed "join_clause" tree
  reference <- mapLeft show (grammarV1ReferenceJoinClauseCore joinTree)
  expression <- onlyComponentExpression production
  productionValue <- case expression of
    GrammarV1IfExpression _ (Just clause) _ _ ->
      Right (grammarV1ProductionJoinClauseCore (locatedValue clause))
    other -> Left (label <> " -- expected if with join clause, got " <> show other)
  equal label reference productionValue

checkStateBindings :: String -> Text -> Either String ()
checkStateBindings label source = do
  (tree, production) <- parseBoth label source
  let bindingTrees = allNamed "state_binding" tree
  reference <- traverse
    (mapLeft show . grammarV1ReferenceStateBindingCore)
    bindingTrees
  expression <- onlyComponentExpression production
  productionValues <- case expression of
    GrammarV1LoopExpression bindings _ _ ->
      Right (map (grammarV1ProductionStateBindingCore . locatedValue) bindings)
    other -> Left (label <> " -- expected loop expression, got " <> show other)
  equal label reference productionValues

checkEmptyBlock :: Either String ()
checkEmptyBlock = do
  (tree, production) <- parseBoth "empty-block" "component C {}"
  referenceBlockTree <- oneNamed "block" tree
  reference <- mapLeft show (grammarV1ReferenceBlockCore referenceBlockTree)
  component <- onlyComponent production
  let productionValue =
        grammarV1ProductionBlockCore (locatedValue (grammarV1ComponentBody component))
  equal "empty-block" reference productionValue

checkMalformedTree :: Either String ()
checkMalformedTree =
  case grammarV1ReferenceBlockCore (GrammarV1ReferenceLiteral "{") of
    Left _ -> Right ()
    Right value -> Left ("malformed block tree decoded as " <> show value)

parseBoth :: String -> Text -> Either String (GrammarV1ReferenceParseTree, GrammarV1SourceFile)
parseBoth label source = do
  let sourceName = Text.pack label
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure (tree, production)

onlyComponent :: GrammarV1SourceFile -> Either String GrammarV1ComponentDecl
onlyComponent sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ComponentDeclaration component -> Right component
    other -> Left ("expected component declaration, got " <> show other)
  declarations -> Left ("expected one declaration, got " <> show (length declarations))

onlyComponentExpression :: GrammarV1SourceFile -> Either String GrammarV1Expression
onlyComponentExpression sourceFile = do
  component <- onlyComponent sourceFile
  case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
    [Located _ (GrammarV1ExpressionStatement expression)] -> Right (locatedValue expression)
    statements -> Left ("expected one expression statement, got " <> show (length statements))

oneNamed :: Text -> GrammarV1ReferenceParseTree -> Either String GrammarV1ReferenceParseTree
oneNamed name tree = case allNamed name tree of
  [value] -> Right value
  values -> Left
    ("expected exactly one " <> Text.unpack name <> ", got " <> show (length values))

allNamed :: Text -> GrammarV1ReferenceParseTree -> [GrammarV1ReferenceParseTree]
allNamed target tree = case tree of
  GrammarV1ReferenceNonterminal name body
    | name == target -> [tree]
    | otherwise -> allNamed target body
  GrammarV1ReferenceSequence values -> concatMap (allNamed target) values
  GrammarV1ReferenceAlternative _ value -> allNamed target value
  GrammarV1ReferenceOptionalSome value -> allNamed target value
  GrammarV1ReferenceRepetition values -> concatMap (allNamed target) values
  GrammarV1ReferenceLiteral _ -> []
  GrammarV1ReferenceLexical _ _ -> []
  GrammarV1ReferenceOptionalNone -> []

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform value = case value of
  Left errorValue -> Left (transform errorValue)
  Right result -> Right result

equal :: (Eq a, Show a) => String -> a -> a -> Either String ()
equal label reference production
  | reference == production = Right ()
  | otherwise = Left
      (label <> " -- certified/production mismatch\nreference: "
        <> show reference <> "\nproduction: " <> show production)
