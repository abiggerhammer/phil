{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Char (isAlphaNum, isLetter)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  grammar <- TextIO.readFile "grammar/phase1-surface.ebnf"
  results <- sequence
    [ test "SURF-004 reserved words match exact Grammar-v1 identifier literals"
        (reservedWordsMatchGrammar grammar)
    , test "SURF-004 keyword and identifier boundary is exact" keywordBoundary
    , test "SURF-004 UINT_TYPE takes priority over identifiers" uintPriority
    , test "SURF-004 SINT_TYPE and floating type keywords take exact priority" numericTypePriority
    , test "EXEC-022/023 Char and String are exact primitive keywords" textTypePriority
    , test "SURF-004 integer and floating literal classes remain distinct" numericLiteralPriority
    , test "SURF-004 decimal token cannot split an adjacent identifier" decimalBoundary
    , test "SURF-004 Unicode identifier contract is accepted" unicodeIdentifier
    , test "SURF-003 string literal admitted escapes decode exactly" stringEscapes
    , test "EXEC-024 Unicode scalar string escapes preserve exact sequence" unicodeStringEscapes
    , test "EXEC-024 character literals decode exactly one Unicode scalar" characterLiterals
    , test "EXEC-024 malformed and nonscalar character literals reject" invalidCharacterLiteralsReject
    , test "SURF-003 unknown string escape rejects" invalidEscapeRejects
    , test "SURF-003 raw newline in string rejects" rawNewlineRejects
    , test "SURF-003 Unicode whitespace and line comments are trivia" triviaIsNonsemantic
    , test "SURF-004 longest punctuation tokens win" punctuationPriority
    , test "EXEC-021 shift punctuation is maximal and distinct" shiftPunctuation
    , test "SURF-004 division/remainder punctuation coexists with line comments" numericPunctuation
    , test "SURF-003 unknown lexical character fails closed" unknownCharacterRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

reservedWordsMatchGrammar :: Text -> Either String ()
reservedWordsMatchGrammar grammar =
  assert (grammarWords == grammarV1ReservedWords) $
    "reserved-word mismatch: missing="
      <> show (Set.toAscList (grammarWords Set.\\ grammarV1ReservedWords))
      <> ", extra="
      <> show (Set.toAscList (grammarV1ReservedWords Set.\\ grammarWords))
  where
    productionLines =
      [ line
      | line <- Text.lines grammar
      , not ("#" `Text.isPrefixOf` Text.stripStart line)
      ]
    grammarWords = Set.fromList
      [ literal
      | line <- productionLines
      , literal <- quotedLiterals line
      , isIdentifierLiteral literal
      ]

quotedLiterals :: Text -> [Text]
quotedLiterals line = oddPieces (Text.splitOn "\"" line)
  where
    oddPieces (_before : quoted : rest) = quoted : oddPieces rest
    oddPieces _ = []

isIdentifierLiteral :: Text -> Bool
isIdentifierLiteral value = case Text.uncons value of
  Nothing -> False
  Just (first, rest) ->
    (isLetter first || first == '_')
      && Text.all isIdentifierContinue rest
  where
    isIdentifierContinue character =
      isAlphaNum character || character == '_' || character == '\''

keywordBoundary :: Either String ()
keywordBoundary = do
  tokens <- tokenValues "mode modeX record record_type convert convertX"
  assert
    (tokens ==
      [ GrammarKeyword "mode"
      , GrammarIdentifier "modeX"
      , GrammarKeyword "record"
      , GrammarIdentifier "record_type"
      , GrammarKeyword "convert"
      , GrammarIdentifier "convertX"
      ])
    ("unexpected keyword boundary tokens: " <> show tokens)

uintPriority :: Either String ()
uintPriority = do
  tokens <- tokenValues "U32 U32name U999999999999999999999999"
  assert
    (tokens ==
      [ GrammarUIntType "U32"
      , GrammarIdentifier "U32name"
      , GrammarUIntType "U999999999999999999999999"
      ])
    ("unexpected UINT priority tokens: " <> show tokens)

numericTypePriority :: Either String ()
numericTypePriority = do
  tokens <- tokenValues "I8 I32 I32name I999999999999999999999999 F32 F32name F64"
  assert
    (tokens ==
      [ GrammarSIntType "I8"
      , GrammarSIntType "I32"
      , GrammarIdentifier "I32name"
      , GrammarSIntType "I999999999999999999999999"
      , GrammarFloatType "F32"
      , GrammarIdentifier "F32name"
      , GrammarFloatType "F64"
      ])
    ("unexpected signed/float type priority tokens: " <> show tokens)

textTypePriority :: Either String ()
textTypePriority = do
  tokens <- tokenValues "Char CharValue String StringValue"
  assert
    (tokens ==
      [ GrammarKeyword "Char"
      , GrammarIdentifier "CharValue"
      , GrammarStringType "String"
      , GrammarIdentifier "StringValue"
      ])
    ("unexpected text type priority tokens: " <> show tokens)

numericLiteralPriority :: Either String ()
numericLiteralPriority = do
  tokens <- tokenValues "0 1.0 255.25 999999999999999999999999.0001"
  assert
    (tokens ==
      [ GrammarDecimalInteger "0"
      , GrammarDecimalFloat "1.0"
      , GrammarDecimalFloat "255.25"
      , GrammarDecimalFloat "999999999999999999999999.0001"
      ])
    ("unexpected numeric literal tokens: " <> show tokens)
  expectLexReject "1.0x"

decimalBoundary :: Either String ()
decimalBoundary =
  expectLexReject "123abc"

unicodeIdentifier :: Either String ()
unicodeIdentifier = do
  tokens <- tokenValues "λ_name'7"
  assert (tokens == [GrammarIdentifier "λ_name'7"])
    ("unexpected Unicode identifier tokens: " <> show tokens)

stringEscapes :: Either String ()
stringEscapes = do
  tokens <- tokenValues "\"quote\\\" slash\\\\ line\\n return\\r tab\\t\""
  assert
    (tokens == [GrammarString "quote\" slash\\ line\n return\r tab\t"])
    ("unexpected decoded string token: " <> show tokens)

unicodeStringEscapes :: Either String ()
unicodeStringEscapes = do
  tokens <- tokenValues "\"\\u{00e9}\" \"e\\u{0301}\" \"quote: \\\"\""
  assert
    (tokens ==
      [ GrammarString "é"
      , GrammarString "é"
      , GrammarString "quote: \""
      ])
    ("unexpected Unicode string tokens: " <> show tokens)
  assert (GrammarString "é" /= GrammarString "é")
    "canonically equivalent strings were normalized during lexing"
  expectLexReject "\"\\u{d800}\""
  expectLexReject "\"\\u{110000}\""
  expectLexReject "\"\\u{}\""

characterLiterals :: Either String ()
characterLiterals = do
  tokens <- tokenValues "'A' 'λ' '😀' '\\n' '\\\\' '\\u{03bb}' '\"'"
  assert
    (tokens ==
      [ GrammarChar "A"
      , GrammarChar "λ"
      , GrammarChar "😀"
      , GrammarChar "\n"
      , GrammarChar "\\"
      , GrammarChar "λ"
      , GrammarChar "\""
      ])
    ("unexpected character literal tokens: " <> show tokens)

invalidCharacterLiteralsReject :: Either String ()
invalidCharacterLiteralsReject = do
  expectLexReject "''"
  expectLexReject "'ab'"
  expectLexReject "'\\u{d800}'"
  expectLexReject "'\\u{110000}'"
  expectLexReject "'\\u{}'"
  expectLexReject "'\\x'"

invalidEscapeRejects :: Either String ()
invalidEscapeRejects =
  expectLexReject "\"bad\\x\""

rawNewlineRejects :: Either String ()
rawNewlineRejects =
  expectLexReject "\"first\nsecond\""

triviaIsNonsemantic :: Either String ()
triviaIsNonsemantic = do
  tokens <- tokenValues "\x2003record // ignored comment\n\tName"
  assert
    (tokens == [GrammarKeyword "record", GrammarIdentifier "Name"])
    ("unexpected trivia tokens: " <> show tokens)

punctuationPriority :: Either String ()
punctuationPriority = do
  tokens <- tokenValues "x==y => z->w <= 2 != 3 >= 1"
  assert
    (tokens ==
      [ GrammarIdentifier "x"
      , GrammarSymbol "=="
      , GrammarIdentifier "y"
      , GrammarSymbol "=>"
      , GrammarIdentifier "z"
      , GrammarSymbol "->"
      , GrammarIdentifier "w"
      , GrammarSymbol "<="
      , GrammarDecimalInteger "2"
      , GrammarSymbol "!="
      , GrammarDecimalInteger "3"
      , GrammarSymbol ">="
      , GrammarDecimalInteger "1"
      ])
    ("unexpected punctuation tokens: " <> show tokens)

shiftPunctuation :: Either String ()
shiftPunctuation = do
  tokens <- tokenValues "a << 1 >> b < c > d"
  assert
    (tokens ==
      [ GrammarIdentifier "a"
      , GrammarSymbol "<<"
      , GrammarDecimalInteger "1"
      , GrammarSymbol ">>"
      , GrammarIdentifier "b"
      , GrammarSymbol "<"
      , GrammarIdentifier "c"
      , GrammarSymbol ">"
      , GrammarIdentifier "d"
      ])
    ("unexpected shift punctuation tokens: " <> show tokens)

numericPunctuation :: Either String ()
numericPunctuation = do
  tokens <- tokenValues "x / y % z // comment\n * w"
  assert
    (tokens ==
      [ GrammarIdentifier "x"
      , GrammarSymbol "/"
      , GrammarIdentifier "y"
      , GrammarSymbol "%"
      , GrammarIdentifier "z"
      , GrammarSymbol "*"
      , GrammarIdentifier "w"
      ])
    ("unexpected numeric punctuation/comment tokens: " <> show tokens)

unknownCharacterRejects :: Either String ()
unknownCharacterRejects =
  expectLexReject "record Name {} $"

tokenValues :: Text -> Either String [GrammarV1Token]
tokenValues source =
  map (\(Located _ token) -> token) <$> mapLeft show (lexGrammarV1 "surf004" source)

expectLexReject :: Text -> Either String ()
expectLexReject source = case lexGrammarV1 "surf004" source of
  Left _ -> Right ()
  Right tokens -> Left ("expected lexical rejection, got " <> show tokens)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
