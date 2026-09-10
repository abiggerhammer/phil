{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Char (isAsciiUpper)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer
  ( GrammarV1Token (..)
  , lexGrammarV1
  , lexGrammarV1SourceTokens
  , runtimeBytesLengthMarker
  )
import Phil.Surface.GrammarV1.ReferenceToken
  ( GrammarV1ReferenceToken (..)
  , lexGrammarV1ReferenceTokens
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  grammar <- TextIO.readFile "grammar/phase1-surface.ebnf"
  results <- sequence
    [ test "GRAMMAR-CORR lexical classes are exhaustively bridged"
        (lexicalClassesMatchBridge grammar)
    , test "GRAMMAR-CORR every Grammar-v1 literal projects as TLiteral shape"
        (allGrammarLiteralsProjectExactly grammar)
    , test "GRAMMAR-CORR lexical classes preserve exact decoded lexemes"
        lexicalClassProjection
    , test "GRAMMAR-CORR primitive keyword carriers remain grammar literals"
        primitiveKeywordProjection
    , test "GRAMMAR-CORR reference projection preserves source token spans"
        referenceSpansPreserved
    , test "GRAMMAR-CORR bare Bytes normalization stays production-only"
        bareBytesNormalizationBoundary
    , test "GRAMMAR-CORR explicit Bytes index is token preserving"
        explicitBytesIndexPreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

lexicalClassesMatchBridge :: Text -> Either String ()
lexicalClassesMatchBridge grammar =
  assert (actual == expected) $
    "unexpected Grammar-v1 lexical classes: actual=" <> show actual
      <> ", expected=" <> show expected
  where
    actual = grammarLexicalClasses grammar
    expected = Set.fromList
      [ "IDENTIFIER"
      , "DECIMAL_INTEGER"
      , "DECIMAL_FLOAT"
      , "STRING_LITERAL"
      , "CHAR_LITERAL"
      , "UINT_TYPE"
      , "SINT_TYPE"
      ]

allGrammarLiteralsProjectExactly :: Text -> Either String ()
allGrammarLiteralsProjectExactly grammar =
  mapM_ checkLiteral (Set.toAscList (grammarLiterals grammar))
  where
    checkLiteral literal = do
      tokens <- referenceValues literal
      assert (tokens == [GrammarV1LiteralToken literal]) $
        "literal " <> show literal <> " projected as " <> show tokens

lexicalClassProjection :: Either String ()
lexicalClassProjection = do
  tokens <- referenceValues "name 42 1.25 \"e\\u{0301}\" '\\u{03bb}' U32 I64"
  let expected =
        [ GrammarV1LexicalToken "IDENTIFIER" "name"
        , GrammarV1LexicalToken "DECIMAL_INTEGER" "42"
        , GrammarV1LexicalToken "DECIMAL_FLOAT" "1.25"
        , GrammarV1LexicalToken "STRING_LITERAL" "é"
        , GrammarV1LexicalToken "CHAR_LITERAL" "λ"
        , GrammarV1LexicalToken "UINT_TYPE" "U32"
        , GrammarV1LexicalToken "SINT_TYPE" "I64"
        ]
  assert (tokens == expected) $
    "unexpected lexical-class projection: " <> show tokens

primitiveKeywordProjection :: Either String ()
primitiveKeywordProjection = do
  tokens <- referenceValues "F32 F64 String Char Bytes"
  let expected = map GrammarV1LiteralToken ["F32", "F64", "String", "Char", "Bytes"]
  assert (tokens == expected) $
    "primitive grammar literals were reclassified: " <> show tokens

referenceSpansPreserved :: Either String ()
referenceSpansPreserved = do
  sourceTokens <- mapLeft show $
    lexGrammarV1SourceTokens "span-test.phil" "module Demo; // trivia\nrecord Value {}"
  referenceTokens <- mapLeft show $
    lexGrammarV1ReferenceTokens "span-test.phil" "module Demo; // trivia\nrecord Value {}"
  let sourceSpans = map (\(Located span' _) -> span') sourceTokens
      referenceSpans = map (\(Located span' _) -> span') referenceTokens
  assert (sourceSpans == referenceSpans) $
    "reference projection changed source spans: source=" <> show sourceSpans
      <> ", reference=" <> show referenceSpans

bareBytesNormalizationBoundary :: Either String ()
bareBytesNormalizationBoundary = do
  sourceTokens <- sourceValues "Bytes"
  referenceTokens <- referenceValues "Bytes"
  productionTokens <- productionValues "Bytes"
  assert (sourceTokens == [GrammarKeyword "Bytes"]) $
    "canonical source tokens unexpectedly normalized bare Bytes: " <> show sourceTokens
  assert (referenceTokens == [GrammarV1LiteralToken "Bytes"]) $
    "reference stream contains production normalization: " <> show referenceTokens
  assert
    (productionTokens ==
      [ GrammarKeyword "Bytes"
      , GrammarSymbol "["
      , GrammarDecimalInteger runtimeBytesLengthMarker
      , GrammarSymbol "]"
      ]) $
    "production bare-Bytes compatibility normalization changed: " <> show productionTokens

explicitBytesIndexPreserved :: Either String ()
explicitBytesIndexPreserved = do
  sourceTokens <- sourceValues "Bytes[8]"
  productionTokens <- productionValues "Bytes[8]"
  referenceTokens <- referenceValues "Bytes[8]"
  assert (sourceTokens == productionTokens) $
    "explicit Bytes index was changed by production normalization: source="
      <> show sourceTokens <> ", production=" <> show productionTokens
  assert
    (referenceTokens ==
      [ GrammarV1LiteralToken "Bytes"
      , GrammarV1LiteralToken "["
      , GrammarV1LexicalToken "DECIMAL_INTEGER" "8"
      , GrammarV1LiteralToken "]"
      ]) $
    "unexpected explicit Bytes reference tokens: " <> show referenceTokens

grammarProductionLines :: Text -> [Text]
grammarProductionLines grammar =
  [ line
  | line <- Text.lines grammar
  , not ("#" `Text.isPrefixOf` Text.stripStart line)
  ]

grammarLiterals :: Text -> Set.Set Text
grammarLiterals =
  Set.fromList . concatMap quotedLiterals . grammarProductionLines

grammarLexicalClasses :: Text -> Set.Set Text
grammarLexicalClasses =
  Set.fromList . concatMap angleClasses . grammarProductionLines

quotedLiterals :: Text -> [Text]
quotedLiterals line = oddPieces (Text.splitOn "\"" line)
  where
    oddPieces (_before : quoted : rest) = quoted : oddPieces rest
    oddPieces _ = []

angleClasses :: Text -> [Text]
angleClasses input = case Text.breakOn "<" input of
  (_, rest) | Text.null rest -> []
  (_, rest) ->
    let afterOpen = Text.drop 1 rest
        (candidate, closeAndRest) = Text.breakOn ">" afterOpen
        tailText = if Text.null closeAndRest then "" else Text.drop 1 closeAndRest
        candidateIsClass =
          not (Text.null candidate)
            && Text.all (\character -> isAsciiUpper character || character == '_') candidate
    in (if candidateIsClass then [candidate] else []) <> angleClasses tailText

sourceValues :: Text -> Either String [GrammarV1Token]
sourceValues input =
  map (\(Located _ token) -> token)
    <$> mapLeft show (lexGrammarV1SourceTokens "grammar-corr" input)

productionValues :: Text -> Either String [GrammarV1Token]
productionValues input =
  map (\(Located _ token) -> token)
    <$> mapLeft show (lexGrammarV1 "grammar-corr" input)

referenceValues :: Text -> Either String [GrammarV1ReferenceToken]
referenceValues input =
  map (\(Located _ token) -> token)
    <$> mapLeft show (lexGrammarV1ReferenceTokens "grammar-corr" input)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
