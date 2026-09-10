{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1Expression
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstBlockCommands
  ( grammarV1ProductionBlockCommand
  , grammarV1ReferenceBlockCommand
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceParseSourceTokens
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  let cases =
        [ ("borrow", "borrow owner as view { return view; }")
        , ("if-minimal", "if cond { return 1; }")
        , ("if-rich", "if cond join state (x: U8) invariant x == x { return x; } else { return 0; }")
        , ("match", "match value join state (x: U8) invariant true { Some(v) => return v; None => { return 0; } }")
        , ("decide", "decide verdict { Yes() => return 1; No{reason as r,} => { return 0; } }")
        , ("closure-minimal", "closure () satisfies Callable { return unit; }")
        , ("closure-rich", "closure mode affine (x: U8, y: Bytes[4]) satisfies Callable captures (x, y) { let z = x; return z; }")
        , ("closure-empty-captures", "closure () satisfies Callable captures () { return unit; }")
        , ("loop-minimal", "loop { break; }")
        , ("loop-empty-state", "loop state () { break(); }")
        , ("loop-rich", "loop state (i: U8 = 0, n = 4) invariant i < n { continue(i + 1, n); }")
        , ("offer", "offer endpoint { Left(v) => return v; Right{value as x,} => { return x; } }")
        ]
      results = [checkCase label command | (label, command) <- cases]
      unsupported = checkUnsupportedCommand
      malformed = case grammarV1ReferenceBlockCommand
        (GrammarV1ReferenceNonterminal "command_expression"
          (GrammarV1ReferenceAlternative 27
            (GrammarV1ReferenceLiteral "impossible"))) of
        Left _ -> Right ()
        Right value -> Left ("out-of-range command decoded as " <> show value)
      failures = [detail | Left detail <- results <> [unsupported, malformed]]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: seven block-bearing Grammar-v1 command families agree with production AST ("
        <> show (length cases) <> " direct controls)")
    else exitFailure

checkCase :: String -> Text -> Either String ()
checkCase label command = do
  let source = "type T = Bytes[" <> command <> "];"
      sourceName = Text.pack label
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  commandTree <- maybeToEither "no command_expression in certified tree"
    (firstNamed "command_expression" tree)
  reference <- mapLeft show (grammarV1ReferenceBlockCommand commandTree)
  referenceValue <- maybeToEither "command was outside block-bearing tranche" reference
  productionFile <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  productionExpression <- onlyBytesIndex productionFile
  productionValue <- maybeToEither "production command was outside block-bearing tranche"
    (grammarV1ProductionBlockCommand productionExpression)
  if referenceValue == productionValue
    then Right ()
    else Left
      (label <> " -- certified/production block-command mismatch\nreference: "
        <> show referenceValue <> "\nproduction: " <> show productionValue)

checkUnsupportedCommand :: Either String ()
checkUnsupportedCommand = do
  let source = "type T = Bytes[send value on endpoint];"
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens "unsupported-command" source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  commandTree <- maybeToEither "unsupported control has no command_expression"
    (firstNamed "command_expression" tree)
  reference <- mapLeft show (grammarV1ReferenceBlockCommand commandTree)
  productionFile <- mapLeft show
    (parseGrammarV1StructuralSource "unsupported-command" source)
  productionExpression <- onlyBytesIndex productionFile
  let production = grammarV1ProductionBlockCommand productionExpression
  if reference == Nothing && production == Nothing
    then Right ()
    else Left
      ("fixed command escaped block-bearing tranche: reference="
        <> show reference <> ", production=" <> show production)

onlyBytesIndex :: GrammarV1SourceFile -> Either String GrammarV1Expression
onlyBytesIndex sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration alias ->
      case locatedValue (grammarV1TypeAliasTarget alias) of
        GrammarV1BytesType expression -> Right (locatedValue expression)
        other -> Left ("expected Bytes target, got " <> show other)
    other -> Left ("expected type alias, got " <> show other)
  values -> Left ("expected one top-level declaration, got " <> show (length values))

firstNamed :: Text -> GrammarV1ReferenceParseTree -> Maybe GrammarV1ReferenceParseTree
firstNamed target tree = case tree of
  GrammarV1ReferenceNonterminal name body
    | name == target -> Just tree
    | otherwise -> firstNamed target body
  GrammarV1ReferenceSequence values -> firstInList values
  GrammarV1ReferenceAlternative _ value -> firstNamed target value
  GrammarV1ReferenceOptionalSome value -> firstNamed target value
  GrammarV1ReferenceRepetition values -> firstInList values
  GrammarV1ReferenceLiteral _ -> Nothing
  GrammarV1ReferenceLexical _ _ -> Nothing
  GrammarV1ReferenceOptionalNone -> Nothing
  where
    firstInList [] = Nothing
    firstInList (value : rest) = case firstNamed target value of
      Just found -> Just found
      Nothing -> firstInList rest

maybeToEither :: String -> Maybe a -> Either String a
maybeToEither message value = case value of
  Just result -> Right result
  Nothing -> Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
