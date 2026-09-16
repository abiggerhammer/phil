{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1StaticReference
  , GrammarV1TopLevelDecl (..)
  , GrammarV1Type (..)
  , GrammarV1TypeAliasDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticArgumentClosure
  ( grammarV1StaticArgumentClosureCorresponds
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
        [ ("no-arguments", "Root", 0)
        , ("primitive-type", "Root[U8]", 1)
        , ("nested-type-reference", "Root[Frame[Wire[U16]]]", 2)
        , ( "session-payload"
          , "Root[send (x : Frame[Wire[U8]]) using Boundary[U16] when Claim[U32]() then continue S]"
          , 4
          )
        , ("static-value-payload", "Root[1 + Config[U8, 2] * 3]", 3)
        , ( "effect-payload"
          , "Root[{Read[U8](Call[2]), Write[Frame[Wire[U16]]](x)}]"
          , 5
          )
        , ( "mixed-type-payload"
          , "Root[(Frame[Wire[U8]], Proof[Claim[Config[1]]()])]"
          , 4
          )
        , ( "command-expression-payload"
          , "Root[Bytes[construct Box[U8] {value = Call[2]}]]"
          , 3
          )
        ]
      results =
        [ checkCase label target expected
        | (label, target, expected) <- cases
        ]
      mismatch = checkNestedMismatch
      failures = [detail | Left detail <- results <> [mismatch]]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: recursive Grammar-v1 static arguments agree across "
        <> show (length cases) <> " nested controls")
    else exitFailure

checkCase :: String -> Text -> Int -> Either String ()
checkCase label target expectedCount = do
  let source = "type T = " <> target <> ";"
      sourceName = Text.pack label
  (referenceTree, productionReference) <- parseReferencePair sourceName source
  count <- mapLeft show
    (grammarV1StaticArgumentClosureCorresponds referenceTree productionReference)
  if count == expectedCount
    then Right ()
    else Left
      (label <> " -- expected " <> show expectedCount
        <> " static-argument occurrences, got " <> show count)

-- The outer Root argument and Config reference have identical shallow category
-- shapes in both sources. Only recursively decoding Config's own argument can
-- distinguish these two values.
checkNestedMismatch :: Either String ()
checkNestedMismatch = do
  (referenceTree, _) <- parseReferencePair
    "nested-mismatch-reference"
    "type T = Root[Config[1]];"
  (_, productionReference) <- parseReferencePair
    "nested-mismatch-production"
    "type T = Root[Config[2]];"
  case grammarV1StaticArgumentClosureCorresponds referenceTree productionReference of
    Left _ -> Right ()
    Right count -> Left
      ("nested static-value mismatch escaped closure with count " <> show count)

parseReferencePair
  :: Text
  -> Text
  -> Either String (GrammarV1ReferenceParseTree, GrammarV1StaticReference)
parseReferencePair sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceTree <- maybeToEither "no static_reference node in certified tree"
    (firstNamed "static_reference" tree)
  productionFile <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  productionReference <- onlyNamedTarget productionFile
  pure (referenceTree, productionReference)

onlyNamedTarget :: GrammarV1SourceFile -> Either String GrammarV1StaticReference
onlyNamedTarget sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration alias ->
      case locatedValue (grammarV1TypeAliasTarget alias) of
        GrammarV1NamedType reference -> Right reference
        other -> Left ("expected named type target, got " <> show other)
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
