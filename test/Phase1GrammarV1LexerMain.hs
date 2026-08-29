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
    , test "SURF-004 decimal token cannot split an adjacent identifier" decimalBoundary
    , test "SURF-004 Unicode identifier contract is accepted" unicodeIdentifier
    , test "SURF-003 string literal admitted escapes decode exactly" stringEscapes
    , test "SURF-003 unknown string escape rejects" invalidEscapeRejects
    , test "SURF-003 raw newline in string rejects" rawNewlineRejects
    , test "SURF-003 Unicode whitespace and line comments are trivia" triviaIsNonsemantic
    , test "SURF-004 longest punctuation tokens win" punctuationPriority
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
  tokens <- tokenValues "mode modeX record record_type"
  assert
    (tokens ==
      [ GrammarKeyword "mode"
      , GrammarIdentifier "modeX"
      , GrammarKeyword "record"
      , GrammarIdentifier "record_type"
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
