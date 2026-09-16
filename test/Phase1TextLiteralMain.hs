{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Data.Text (Text)
import Phil.Core.UnicodeChar
  ( unicodeScalarCodePoint
  )
import Phil.Core.UnicodeString
  ( unicodeStringCodePoints
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Declaration (..)
  , GrammarV1Expression (..)
  , pattern GrammarV1CharExpression
  , pattern GrammarV1StringExpression
  , GrammarV1SourceFile (..)
  , GrammarV1Statement (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.TextLiteral
  ( GrammarV1TextLiteralError (..)
  , grammarV1RuntimeCharLiteral
  , grammarV1RuntimeStringLiteral
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-024 ASCII Char source elaborates exactly" asciiChar
    , test "EXEC-024 BMP and supplementary Char source elaborate exactly" unicodeChars
    , test "EXEC-024 Char escapes elaborate to exact scalars" charEscapes
    , test "EXEC-024 empty and mixed String source preserve exact scalar sequence" exactStrings
    , test "EXEC-024 escaped quote is syntax, not a String backslash" escapedStringQuote
    , test "EXEC-024 canonically equivalent String literals remain distinct" noImplicitNormalization
    , test "EXEC-024 numeric leaf cannot masquerade as Char or String" literalCategoriesRemainDistinct
    , test "EXEC-024 malformed and nonscalar Char source rejects" malformedCharsReject
    , test "EXEC-024 malformed and nonscalar String source rejects" malformedStringsReject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

asciiChar :: Either String ()
asciiChar = do
  expression <- parseLiteralExpression "'A'"
  assert (expression == GrammarV1CharExpression "A")
    ("parser did not retain Char literal category: " <> show expression)
  scalar <- mapLeft show (grammarV1RuntimeCharLiteral expression)
  assert (unicodeScalarCodePoint scalar == 0x41)
    "ASCII Char code point changed"

unicodeChars :: Either String ()
unicodeChars = do
  lambda <- charCodePoint "'λ'"
  emoji <- charCodePoint "'😀'"
  assert (lambda == 0x03bb) ("lambda changed: " <> show lambda)
  assert (emoji == 0x1f600) ("supplementary scalar changed: " <> show emoji)

charEscapes :: Either String ()
charEscapes = do
  newline <- charCodePoint "'\\n'"
  backslash <- charCodePoint "'\\\\'"
  unicodeEscape <- charCodePoint "'\\u{03bb}'"
  quote <- charCodePoint "'\"'"
  assert (newline == 0x0a) "\\n did not denote U+000A"
  assert (backslash == 0x5c) "\\\\ did not denote U+005C"
  assert (unicodeEscape == 0x03bb) "Unicode scalar escape changed value"
  assert (quote == 0x22) "double quote inside Char did not denote U+0022"

exactStrings :: Either String ()
exactStrings = do
  empty <- stringCodePoints "\"\""
  mixed <- stringCodePoints "\"A😀λ\""
  assert (empty == []) ("empty String changed: " <> show empty)
  assert (mixed == [0x41, 0x1f600, 0x03bb])
    ("mixed String changed: " <> show mixed)

escapedStringQuote :: Either String ()
escapedStringQuote = do
  expression <- parseLiteralExpression "\"\\\"\""
  assert (expression == GrammarV1StringExpression "\"")
    ("runtime String literal category/content drifted: " <> show expression)
  codePoints <- mapLeft show $
    unicodeStringCodePoints <$> grammarV1RuntimeStringLiteral expression
  assert (codePoints == [0x22])
    ("escaped quote produced extra syntax content: " <> show codePoints)

noImplicitNormalization :: Either String ()
noImplicitNormalization = do
  composedExpression <- parseLiteralExpression "\"é\""
  decomposedExpression <- parseLiteralExpression "\"e\\u{0301}\""
  composed <- mapLeft show (grammarV1RuntimeStringLiteral composedExpression)
  decomposed <- mapLeft show (grammarV1RuntimeStringLiteral decomposedExpression)
  assert (unicodeStringCodePoints composed == [0x00e9])
    "composed String scalar sequence changed"
  assert (unicodeStringCodePoints decomposed == [0x0065, 0x0301])
    "decomposed String scalar sequence changed"
  assert (composed /= decomposed)
    "canonically equivalent String literals were normalized implicitly"

literalCategoriesRemainDistinct :: Either String ()
literalCategoriesRemainDistinct = do
  integer <- parseLiteralExpression "65"
  case grammarV1RuntimeCharLiteral integer of
    Left (GrammarV1RuntimeCharLiteralRequired _) -> Right ()
    other -> Left ("integer entered Char literal semantics: " <> show other)
  case grammarV1RuntimeStringLiteral integer of
    Left (GrammarV1RuntimeStringLiteralRequired _) -> Right ()
    other -> Left ("integer entered String literal semantics: " <> show other)

malformedCharsReject :: Either String ()
malformedCharsReject = do
  mapM_ expectSourceReject
    [ "''"
    , "'ab'"
    , "'\\u{d800}'"
    , "'\\u{110000}'"
    , "'\\u{}'"
    , "'\\x'"
    ]

malformedStringsReject :: Either String ()
malformedStringsReject = do
  mapM_ expectSourceReject
    [ "\"\\u{d800}\""
    , "\"\\u{110000}\""
    , "\"\\u{}\""
    , "\"bad\\x\""
    ]

charCodePoint :: Text -> Either String Integer
charCodePoint source = do
  expression <- parseLiteralExpression source
  scalar <- mapLeft show (grammarV1RuntimeCharLiteral expression)
  Right (unicodeScalarCodePoint scalar)

stringCodePoints :: Text -> Either String [Integer]
stringCodePoints source = do
  expression <- parseLiteralExpression source
  value <- mapLeft show (grammarV1RuntimeStringLiteral expression)
  Right (unicodeStringCodePoints value)

parseLiteralExpression :: Text -> Either String GrammarV1Expression
parseLiteralExpression literal = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource
      "exec-024.phil"
      ("component C() { " <> literal <> "; }")
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1ComponentDeclaration component ->
        case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
          [Located _ (GrammarV1ExpressionStatement (Located _ expression))] -> Right expression
          statements -> Left ("expected one expression statement, got " <> show statements)
      other -> Left ("expected component declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show declarations)

expectSourceReject :: Text -> Either String ()
expectSourceReject literal =
  case parseGrammarV1StructuralSource
      "exec-024-negative.phil"
      ("component C() { " <> literal <> "; }") of
    Left _ -> Right ()
    Right parsed -> Left ("expected source rejection, got " <> show parsed)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
