{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceAcceptsSource
  , grammarV1ReferenceAcceptsSourceTokens
  , grammarV1ReferenceAcceptsTokens
  , grammarV1ReferenceTokenToKernel
  , textToKernelString
  ) where

import Data.Bits (testBit)
import qualified Data.ByteString as ByteString
import Data.Text (Text)
import qualified Data.Text.Encoding as TextEncoding
import Data.Word (Word8)
import Phil.Surface.GrammarV1.Lexer
  ( GrammarV1LexDiagnostic
  , GrammarV1Token
  )
import Phil.Surface.GrammarV1.ReferenceToken
  ( GrammarV1ReferenceToken (..)
  , grammarV1ReferenceToken
  , lexGrammarV1ReferenceTokens
  )
import Phil.Surface.Syntax (Located (..))
import qualified SurfaceGrammarRecognizerKernel as Kernel

-- | Encode production Unicode Text to the exact byte-oriented Rocq String
-- representation emitted by extraction.  Rocq Ascii stores bit 0 first.
-- UTF-8 is the explicit representation bridge; no Text/String definitional
-- equality is assumed.
textToKernelString :: Text -> Kernel.String
textToKernelString =
  ByteString.foldr
    (Kernel.String0 . byteToKernelAscii)
    Kernel.EmptyString
    . TextEncoding.encodeUtf8

byteToKernelAscii :: Word8 -> Kernel.Ascii0
byteToKernelAscii byte =
  Kernel.Ascii
    (testBit byte 0)
    (testBit byte 1)
    (testBit byte 2)
    (testBit byte 3)
    (testBit byte 4)
    (testBit byte 5)
    (testBit byte 6)
    (testBit byte 7)

-- | Total constructor mapping from the Haskell mirror introduced by #865 to
-- the exact ConcreteToken carrier emitted from GrammarDerivation.v.
grammarV1ReferenceTokenToKernel
  :: GrammarV1ReferenceToken
  -> Kernel.ConcreteToken
grammarV1ReferenceTokenToKernel token = case token of
  GrammarV1LiteralToken literal ->
    Kernel.TLiteral (textToKernelString literal)
  GrammarV1LexicalToken className lexeme ->
    Kernel.TLexical
      (textToKernelString className)
      (textToKernelString lexeme)

grammarV1ReferenceAcceptsTokens
  :: [GrammarV1ReferenceToken]
  -> Bool
grammarV1ReferenceAcceptsTokens =
  Kernel.phase1_surface_reference_accepts
    . map grammarV1ReferenceTokenToKernel

-- | Admit an already-lexed canonical source token stream.  This is the
-- production parser binding point: it cannot observe the synthetic bare-Bytes
-- normalization because the caller supplies #865's pre-normalization tokens.
grammarV1ReferenceAcceptsSourceTokens
  :: [Located GrammarV1Token]
  -> Bool
grammarV1ReferenceAcceptsSourceTokens =
  grammarV1ReferenceAcceptsTokens
    . map (grammarV1ReferenceToken . locatedValue)

-- | Lex at the exact pre-normalization Grammar-v1 source-token boundary from
-- #865, erase source spans, then invoke the extracted certified recognizer.
-- Lexical diagnostics remain available to callers; a production admission gate
-- can fail closed on Left when this staging bridge is promoted.
grammarV1ReferenceAcceptsSource
  :: Text
  -> Text
  -> Either GrammarV1LexDiagnostic Bool
grammarV1ReferenceAcceptsSource source input = do
  locatedTokens <- lexGrammarV1ReferenceTokens source input
  pure
    (grammarV1ReferenceAcceptsTokens
      [token | Located _ token <- locatedTokens])
