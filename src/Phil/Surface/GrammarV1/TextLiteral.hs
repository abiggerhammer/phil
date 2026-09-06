{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.TextLiteral
  ( GrammarV1TextLiteralError (..)
  , grammarV1RuntimeCharLiteral
  , grammarV1RuntimeStringLiteral
  ) where

import Data.Char (ord)
import qualified Data.Text as Text
import Phil.Core.UnicodeChar
  ( UnicodeCharError
  , UnicodeScalar
  , unicodeScalar
  )
import Phil.Core.UnicodeString
  ( UnicodeString
  , unicodeString
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , pattern GrammarV1CharExpression
  , pattern GrammarV1StringExpression
  )

data GrammarV1TextLiteralError
  = GrammarV1RuntimeCharLiteralRequired GrammarV1Expression
  | GrammarV1RuntimeStringLiteralRequired GrammarV1Expression
  | GrammarV1RuntimeCharScalarCount Int
  | GrammarV1RuntimeTextScalarError UnicodeCharError
  deriving (Eq, Show)

-- | EXEC-024 character literals elaborate to exactly one Phil Unicode scalar.
-- The lexer has already decoded source escapes, but this semantic boundary still
-- validates scalar identity independently and rejects malformed injected ASTs.
grammarV1RuntimeCharLiteral
  :: GrammarV1Expression
  -> Either GrammarV1TextLiteralError UnicodeScalar
grammarV1RuntimeCharLiteral expression = case expression of
  GrammarV1CharExpression text -> case Text.unpack text of
    [character] -> scalarFromChar character
    characters -> Left (GrammarV1RuntimeCharScalarCount (length characters))
  _ -> Left (GrammarV1RuntimeCharLiteralRequired expression)

-- | EXEC-024 String literals preserve the exact decoded scalar sequence. No
-- normalization, locale operation, or encoding step is performed here.
grammarV1RuntimeStringLiteral
  :: GrammarV1Expression
  -> Either GrammarV1TextLiteralError UnicodeString
grammarV1RuntimeStringLiteral expression = case expression of
  GrammarV1StringExpression text ->
    unicodeString <$> mapM scalarFromChar (Text.unpack text)
  _ -> Left (GrammarV1RuntimeStringLiteralRequired expression)

scalarFromChar :: Char -> Either GrammarV1TextLiteralError UnicodeScalar
scalarFromChar character =
  mapLeft GrammarV1RuntimeTextScalarError
    (unicodeScalar (toInteger (ord character)))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
