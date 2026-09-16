{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseError (..)
  , GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceAcceptsSource
  , grammarV1ReferenceAcceptsSourceTokens
  , grammarV1ReferenceAcceptsTokens
  , grammarV1ReferenceParseSourceTokens
  , grammarV1ReferenceParseTokens
  , grammarV1ReferenceParseTreeTokens
  , grammarV1ReferenceTokenToKernel
  , kernelStringToText
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

-- | Stable Haskell mirror of the certified structural parse tree emitted by
-- GrammarDerivation.v.  It preserves every grammar-facing choice while
-- replacing the extracted byte-oriented String and Nat carriers with ordinary
-- production Text and Integer values.
data GrammarV1ReferenceParseTree
  = GrammarV1ReferenceLiteral Text
  | GrammarV1ReferenceLexical Text Text
  | GrammarV1ReferenceNonterminal Text GrammarV1ReferenceParseTree
  | GrammarV1ReferenceSequence [GrammarV1ReferenceParseTree]
  | GrammarV1ReferenceAlternative Integer GrammarV1ReferenceParseTree
  | GrammarV1ReferenceOptionalNone
  | GrammarV1ReferenceOptionalSome GrammarV1ReferenceParseTree
  | GrammarV1ReferenceRepetition [GrammarV1ReferenceParseTree]
  deriving (Eq, Show)

data GrammarV1ReferenceParseError
  = GrammarV1ReferenceNoParse
  | GrammarV1ReferenceTrailingTokens Int
  | GrammarV1ReferenceUnexpectedTreeList Int
  | GrammarV1ReferenceInvalidUtf8 [Word8]
  deriving (Eq, Show)

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

-- | Decode an extracted Rocq String under the same explicit UTF-8 contract.
-- Invalid byte strings fail closed rather than being replacement-decoded.
kernelStringToText :: Kernel.String -> Either GrammarV1ReferenceParseError Text
kernelStringToText value =
  let bytes = kernelStringBytes value
  in case TextEncoding.decodeUtf8' (ByteString.pack bytes) of
      Left _ -> Left (GrammarV1ReferenceInvalidUtf8 bytes)
      Right text -> Right text

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

kernelAsciiByte :: Kernel.Ascii0 -> Word8
kernelAsciiByte ascii = case ascii of
  Kernel.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    contribution 0x01 bit0
      + contribution 0x02 bit1
      + contribution 0x04 bit2
      + contribution 0x08 bit3
      + contribution 0x10 bit4
      + contribution 0x20 bit5
      + contribution 0x40 bit6
      + contribution 0x80 bit7
  where
    contribution weight present = if present then weight else 0

kernelStringBytes :: Kernel.String -> [Word8]
kernelStringBytes value = case value of
  Kernel.EmptyString -> []
  Kernel.String0 ascii rest -> kernelAsciiByte ascii : kernelStringBytes rest

kernelNatToInteger :: Kernel.Nat -> Integer
kernelNatToInteger value = case value of
  Kernel.O -> 0
  Kernel.S predecessor -> 1 + kernelNatToInteger predecessor

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

kernelParseTreeToReference
  :: Kernel.ParseTree
  -> Either GrammarV1ReferenceParseError GrammarV1ReferenceParseTree
kernelParseTreeToReference tree = case tree of
  Kernel.PTLiteral literal ->
    GrammarV1ReferenceLiteral <$> kernelStringToText literal
  Kernel.PTLexical className lexeme ->
    GrammarV1ReferenceLexical
      <$> kernelStringToText className
      <*> kernelStringToText lexeme
  Kernel.PTNonterminal name body ->
    GrammarV1ReferenceNonterminal
      <$> kernelStringToText name
      <*> kernelParseTreeToReference body
  Kernel.PTSequence items ->
    GrammarV1ReferenceSequence <$> traverse kernelParseTreeToReference items
  Kernel.PTAlternative index body ->
    GrammarV1ReferenceAlternative
      (kernelNatToInteger index)
      <$> kernelParseTreeToReference body
  Kernel.PTOptionalNone ->
    Right GrammarV1ReferenceOptionalNone
  Kernel.PTOptionalSome body ->
    GrammarV1ReferenceOptionalSome <$> kernelParseTreeToReference body
  Kernel.PTRepetition items ->
    GrammarV1ReferenceRepetition <$> traverse kernelParseTreeToReference items

-- | Decode the exact certified complete parse result.  The production wrapper
-- invokes the start nonterminal with total fuel; a successful complete source
-- parse must therefore return one tree and no unconsumed tokens.
grammarV1ReferenceParseTokens
  :: [GrammarV1ReferenceToken]
  -> Either GrammarV1ReferenceParseError GrammarV1ReferenceParseTree
grammarV1ReferenceParseTokens tokens =
  case Kernel.phase1_surface_reference_parse
    (map grammarV1ReferenceTokenToKernel tokens) of
    Nothing -> Left GrammarV1ReferenceNoParse
    Just (remaining, result) -> case remaining of
      _ : _ -> Left (GrammarV1ReferenceTrailingTokens (length remaining))
      [] -> case result of
        Kernel.ResultTree tree -> kernelParseTreeToReference tree
        Kernel.ResultTrees trees ->
          Left (GrammarV1ReferenceUnexpectedTreeList (length trees))

-- | Decode the certified tree from the exact pre-normalization source-token
-- boundary used by the production admission gate.
grammarV1ReferenceParseSourceTokens
  :: [Located GrammarV1Token]
  -> Either GrammarV1ReferenceParseError GrammarV1ReferenceParseTree
grammarV1ReferenceParseSourceTokens =
  grammarV1ReferenceParseTokens
    . map (grammarV1ReferenceToken . locatedValue)

-- | Recover the source-token leaves of a decoded reference tree.  Structural
-- nodes carry no extra source tokens, so flattening leaves gives the precise
-- token sequence certified by that tree.
grammarV1ReferenceParseTreeTokens
  :: GrammarV1ReferenceParseTree
  -> [GrammarV1ReferenceToken]
grammarV1ReferenceParseTreeTokens tree = case tree of
  GrammarV1ReferenceLiteral literal ->
    [GrammarV1LiteralToken literal]
  GrammarV1ReferenceLexical className lexeme ->
    [GrammarV1LexicalToken className lexeme]
  GrammarV1ReferenceNonterminal _ body ->
    grammarV1ReferenceParseTreeTokens body
  GrammarV1ReferenceSequence items ->
    concatMap grammarV1ReferenceParseTreeTokens items
  GrammarV1ReferenceAlternative _ body ->
    grammarV1ReferenceParseTreeTokens body
  GrammarV1ReferenceOptionalNone ->
    []
  GrammarV1ReferenceOptionalSome body ->
    grammarV1ReferenceParseTreeTokens body
  GrammarV1ReferenceRepetition items ->
    concatMap grammarV1ReferenceParseTreeTokens items

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
grammarV1ReferenceAcceptsSource
  :: Text
  -> Text
  -> Either GrammarV1LexDiagnostic Bool
grammarV1ReferenceAcceptsSource source input = do
  locatedTokens <- lexGrammarV1ReferenceTokens source input
  pure
    (grammarV1ReferenceAcceptsTokens
      [token | Located _ token <- locatedTokens])
