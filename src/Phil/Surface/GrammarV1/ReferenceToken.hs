{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.ReferenceToken
  ( GrammarV1ReferenceToken (..)
  , grammarV1ReferenceToken
  , lexGrammarV1ReferenceTokens
  ) where

import Data.Text (Text)
import Phil.Surface.GrammarV1.Lexer
  ( GrammarV1LexDiagnostic
  , GrammarV1Token (..)
  , lexGrammarV1SourceTokens
  , pattern GrammarChar
  , pattern GrammarDecimalFloat
  , pattern GrammarFloatType
  , pattern GrammarSIntType
  , pattern GrammarStringType
  )
import Phil.Surface.Syntax (Located (..))

-- | Haskell mirror of the proof-side ConcreteToken carrier from
-- GrammarDerivation.v.  Grammar literals retain their exact spelling; lexical
-- classes retain both the exact Grammar-v1 class name and decoded lexeme.
data GrammarV1ReferenceToken
  = GrammarV1LiteralToken Text
  | GrammarV1LexicalToken Text Text
  deriving (Eq, Ord, Show)

-- | Project one canonical source token into the exact two-constructor shape
-- consumed by the Rocq reference recognizer.
grammarV1ReferenceToken :: GrammarV1Token -> GrammarV1ReferenceToken
grammarV1ReferenceToken token = case token of
  GrammarSIntType lexeme ->
    GrammarV1LexicalToken "SINT_TYPE" lexeme
  GrammarFloatType literal ->
    GrammarV1LiteralToken literal
  GrammarStringType literal ->
    GrammarV1LiteralToken literal
  GrammarUIntType lexeme ->
    GrammarV1LexicalToken "UINT_TYPE" lexeme
  GrammarDecimalFloat lexeme ->
    GrammarV1LexicalToken "DECIMAL_FLOAT" lexeme
  GrammarDecimalInteger lexeme ->
    GrammarV1LexicalToken "DECIMAL_INTEGER" lexeme
  GrammarChar lexeme ->
    GrammarV1LexicalToken "CHAR_LITERAL" lexeme
  GrammarSymbol literal ->
    GrammarV1LiteralToken literal
  GrammarKeyword literal ->
    GrammarV1LiteralToken literal
  GrammarIdentifier lexeme ->
    GrammarV1LexicalToken "IDENTIFIER" lexeme
  GrammarString lexeme ->
    GrammarV1LexicalToken "STRING_LITERAL" lexeme

-- | Lex source exactly as Grammar v1 specifies and project its located tokens
-- to the reference-recognizer carrier.  In particular, this intentionally runs
-- before the production parser's synthetic bare-Bytes normalization.
lexGrammarV1ReferenceTokens
  :: Text
  -> Text
  -> Either GrammarV1LexDiagnostic [Located GrammarV1ReferenceToken]
lexGrammarV1ReferenceTokens source input =
  map projectLocated <$> lexGrammarV1SourceTokens source input
  where
    projectLocated (Located span' token) =
      Located span' (grammarV1ReferenceToken token)
