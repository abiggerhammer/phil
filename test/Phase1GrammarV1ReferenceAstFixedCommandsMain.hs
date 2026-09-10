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
import Phil.Surface.GrammarV1.ReferenceAstFixedCommands
  ( grammarV1ProductionFixedCommand
  , grammarV1ReferenceFixedCommand
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
        [ ("receive-frame", "receive_frame(endpoint)")
        , ("receive-exact", "receive_exact 4 using evidence on endpoint")
        , ("receive-exact-no-evidence", "receive_exact 4 on endpoint")
        , ("receive", "receive Bytes[4] on endpoint")
        , ("recognize", "recognize Decoder[U8] from input")
        , ("validate", "validate Validator at offset + 1 on endpoint")
        , ("validate-no-position", "validate Validator on endpoint")
        , ("send-exact", "send_exact value on endpoint")
        , ("send", "send value on endpoint")
        , ("commit-receive", "commit_receive pending using evidence")
        , ("reject", "reject reason")
        , ("close", "close endpoint")
        , ("release", "release value")
        , ("convert", "convert value + 1 to I32")
        , ("transport", "transport value to Validated[Validator, 0, 8] using proofValue")
        , ("accept", "accept bytes as Frame[Codec]")
        , ("prove", "prove(x << 1 == y >> 2)")
        ]
      results = [checkCase label command | (label, command) <- cases]
      unsupported = checkUnsupportedCommand
      malformed = case grammarV1ReferenceFixedCommand
        (GrammarV1ReferenceNonterminal "command_expression"
          (GrammarV1ReferenceAlternative 27
            (GrammarV1ReferenceLiteral "impossible"))) of
        Left _ -> Right ()
        Right value -> Left ("out-of-range command decoded as " <> show value)
      failures = [detail | Left detail <- results <> [unsupported, malformed]]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: 15 fixed-shape Grammar-v1 command families agree with production AST ("
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
  reference <- mapLeft show (grammarV1ReferenceFixedCommand commandTree)
  referenceValue <- maybeToEither "command was outside fixed-shape tranche" reference
  productionFile <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  productionExpression <- onlyBytesIndex productionFile
  productionValue <- maybeToEither "production command was outside fixed-shape tranche"
    (grammarV1ProductionFixedCommand productionExpression)
  if referenceValue == productionValue
    then Right ()
    else Left
      (label <> " -- certified/production fixed-command mismatch\nreference: "
        <> show referenceValue <> "\nproduction: " <> show productionValue)

checkUnsupportedCommand :: Either String ()
checkUnsupportedCommand = do
  let source = "type T = Bytes[construct Pair {left = 1, right = 2}];"
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens "unsupported-command" source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  commandTree <- maybeToEither "unsupported control has no command_expression"
    (firstNamed "command_expression" tree)
  reference <- mapLeft show (grammarV1ReferenceFixedCommand commandTree)
  productionFile <- mapLeft show
    (parseGrammarV1StructuralSource "unsupported-command" source)
  productionExpression <- onlyBytesIndex productionFile
  let production = grammarV1ProductionFixedCommand productionExpression
  if reference == Nothing && production == Nothing
    then Right ()
    else Left
      ("construct command escaped fixed-shape tranche: reference="
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
