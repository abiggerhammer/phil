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
import Phil.Surface.GrammarV1.ReferenceAstCommandClosure
  ( grammarV1CommandClosureCorresponds
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
        [ ("no-command", "x + 1", 0)
        , ("single-command", "close endpoint", 1)
        , ("nested-command-type", "convert close endpoint to Bytes[send value on channel]", 3)
        , ("static-type-argument", "Call[Bytes[close endpoint]]", 1)
        , ("static-effect-argument", "Call[{Close(close endpoint)}]", 1)
        , ("static-session-argument", "Call[send (x : Bytes[close endpoint]) then end Done]", 1)
        , ("static-proof-argument", "Call[Proof[Claim(close endpoint)]]", 1)
        , ("block-recursion", "if cond { return close endpoint; } else { return send value on channel; }", 3)
        , ("loop-recursion", "loop state (i = close endpoint) { return convert send value on channel to Bytes[release n]; }", 5)
        , ("term-arguments", "Call(close x, send y on z)", 2)
        , ("fallback-command", "value or reject close endpoint", 1)
        , ("construct-recursion", "construct Pair {left = close x, right = send y on z}", 3)
        , ("match-recursion", "match close value { Some(v) => return send v on ch; None => { release other; } }", 4)
        ]
      results = [checkCase label expression expected | (label, expression, expected) <- cases]
      mismatch = checkMismatch
      failures = [detail | Left detail <- results <> [mismatch]]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: recursive Grammar-v1 command closure agrees across "
        <> show (length cases) <> " nested controls")
    else exitFailure

checkCase :: String -> Text -> Int -> Either String ()
checkCase label expression expectedCount = do
  let source = "type T = Bytes[" <> expression <> "];"
      sourceName = Text.pack label
  (referenceExpression, productionExpression) <- parseExpressionPair sourceName source
  count <- mapLeft show
    (grammarV1CommandClosureCorresponds referenceExpression productionExpression)
  if count == expectedCount
    then Right ()
    else Left
      (label <> " -- expected " <> show expectedCount
        <> " command occurrences, got " <> show count)

checkMismatch :: Either String ()
checkMismatch = do
  (referenceExpression, _) <- parseExpressionPair
    "mismatch-reference"
    "type T = Bytes[close endpoint];"
  (_, productionExpression) <- parseExpressionPair
    "mismatch-production"
    "type T = Bytes[release endpoint];"
  case grammarV1CommandClosureCorresponds referenceExpression productionExpression of
    Left _ -> Right ()
    Right count -> Left
      ("mismatched command families were accepted with count " <> show count)

parseExpressionPair
  :: Text
  -> Text
  -> Either String (GrammarV1ReferenceParseTree, Located GrammarV1Expression)
parseExpressionPair sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceExpression <- maybeToEither "no expression node in certified tree"
    (firstNamed "expression" tree)
  productionFile <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  productionExpression <- onlyBytesIndex productionFile
  pure (referenceExpression, productionExpression)

onlyBytesIndex
  :: GrammarV1SourceFile
  -> Either String (Located GrammarV1Expression)
onlyBytesIndex sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration alias ->
      case locatedValue (grammarV1TypeAliasTarget alias) of
        GrammarV1BytesType expression -> Right expression
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
