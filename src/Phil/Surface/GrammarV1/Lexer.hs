{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.Lexer
  ( GrammarV1Token (..)
  , GrammarV1LexDiagnostic (..)
  , grammarV1ReservedWords
  , lexGrammarV1
  ) where

import Control.Applicative (empty)
import Control.Monad (void)
import Data.List (sortOn)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void)
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  )
import qualified Text.Megaparsec as MP
import Text.Megaparsec ((<|>))
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = MP.Parsec Void Text

data GrammarV1Token
  = GrammarKeyword Text
  | GrammarIdentifier Text
  | GrammarUIntType Text
  | GrammarDecimalInteger Text
  | GrammarString Text
  | GrammarSymbol Text
  deriving (Eq, Ord, Show)

data GrammarV1LexDiagnostic = GrammarV1LexDiagnostic
  { grammarV1LexDiagnosticPoint :: SourcePoint
  , grammarV1LexDiagnosticMessage :: Text
  }
  deriving (Eq, Show)

grammarV1ReservedWords :: Set.Set Text
grammarV1ReservedWords = Set.fromList
  [ "Bool"
  , "Bytes"
  , "Effects"
  , "Frame"
  , "Message"
  , "Nat"
  , "Proof"
  , "Session"
  , "Type"
  , "Unit"
  , "Validated"
  , "accept"
  , "affine"
  , "and"
  , "architecture"
  , "as"
  , "assume"
  , "assumes"
  , "at"
  , "authority"
  , "bind"
  , "borrow"
  , "borrows"
  , "boundary"
  , "break"
  , "callee"
  , "callable"
  , "canonical"
  , "capability"
  , "captures"
  , "claim"
  , "close"
  , "commit_receive"
  , "component"
  , "constraint"
  , "construct"
  , "consume"
  , "consumes"
  , "continue"
  , "correspondence"
  , "cost"
  , "data"
  , "decide"
  , "disjoint"
  , "effects"
  , "else"
  , "end"
  , "ensures"
  , "entry"
  , "environment"
  , "export"
  , "external"
  , "fail"
  , "failure"
  , "false"
  , "fatal"
  , "fn"
  , "from"
  , "grant"
  , "if"
  , "implementation"
  , "import"
  , "in"
  , "instance"
  , "instantiate"
  , "invariant"
  , "join"
  , "law"
  , "let"
  , "lifecycle"
  , "linear"
  , "loop"
  , "match"
  , "mode"
  , "module"
  , "negative"
  , "not"
  , "obligation"
  , "observable"
  , "offer"
  , "on"
  , "opaque"
  , "operation"
  , "or"
  , "originates"
  , "outcome"
  , "outcomes"
  , "permits"
  , "placement"
  , "preserve"
  , "process"
  , "program"
  , "proposition"
  , "protocol"
  , "provider"
  , "provides"
  , "prove"
  , "receive"
  , "receive_exact"
  , "receive_frame"
  , "recognize"
  , "record"
  , "recursive"
  , "ref"
  , "reject"
  , "release"
  , "replace"
  , "representation"
  , "requires"
  , "return"
  , "role"
  , "satisfies"
  , "select"
  , "send"
  , "send_exact"
  , "state"
  , "structural"
  , "success"
  , "terminal"
  , "then"
  , "to"
  , "transport"
  , "true"
  , "type"
  , "unit"
  , "unrestricted"
  , "using"
  , "validate"
  , "when"
  , "with"
  , "within"
  ]

lexGrammarV1 :: Text -> Text -> Either GrammarV1LexDiagnostic [Located GrammarV1Token]
lexGrammarV1 source input =
  case MP.runParser (spaceConsumer *> MP.many pLocatedToken <* MP.eof) (Text.unpack source) input of
    Right tokens -> Right tokens
    Left bundle -> Left (diagnosticFromBundle bundle)

spaceConsumer :: Parser ()
spaceConsumer = Lexer.space MPC.space1 (Lexer.skipLineComment "//") empty

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaceConsumer

pLocatedToken :: Parser (Located GrammarV1Token)
pLocatedToken = do
  start <- currentPoint
  token <- lexeme pToken
  end <- currentPoint
  pure (Located (SourceSpan start end) token)

pToken :: Parser GrammarV1Token
pToken = MP.choice
  [ MP.try pString
  , MP.try pUIntType
  , MP.try pDecimalInteger
  , MP.try pIdentifierOrKeyword
  , pSymbol
  ]

pUIntType :: Parser GrammarV1Token
pUIntType = do
  void (MPC.char 'U')
  digits <- Text.pack <$> MP.some MPC.digitChar
  MP.notFollowedBy identifierContinue
  pure (GrammarUIntType ("U" <> digits))

pDecimalInteger :: Parser GrammarV1Token
pDecimalInteger = do
  digits <- Text.pack <$> MP.some MPC.digitChar
  MP.notFollowedBy identifierContinue
  pure (GrammarDecimalInteger digits)

pIdentifierOrKeyword :: Parser GrammarV1Token
pIdentifierOrKeyword = do
  name <- Text.pack <$> ((:) <$> identifierStart <*> MP.many identifierContinue)
  pure $
    if Set.member name grammarV1ReservedWords
      then GrammarKeyword name
      else GrammarIdentifier name

identifierStart :: Parser Char
identifierStart = MPC.letterChar <|> MPC.char '_'

identifierContinue :: Parser Char
identifierContinue = MPC.alphaNumChar <|> MPC.char '_' <|> MPC.char '\''

pString :: Parser GrammarV1Token
pString = GrammarString . Text.pack <$> MP.between (MPC.char '"') (MPC.char '"') (MP.many pStringChar)

pStringChar :: Parser Char
pStringChar =
  MP.choice
    [ MPC.char '\\' *> pEscape
    , MP.satisfy (\character -> character /= '"' && character /= '\\' && character /= '\n' && character /= '\r')
    ]

pEscape :: Parser Char
pEscape = MP.choice
  [ '"' <$ MPC.char '"'
  , '\\' <$ MPC.char '\\'
  , '\n' <$ MPC.char 'n'
  , '\r' <$ MPC.char 'r'
  , '\t' <$ MPC.char 't'
  ]

pSymbol :: Parser GrammarV1Token
pSymbol = GrammarSymbol <$> MP.choice (map MP.chunk orderedSymbols)
  where
    orderedSymbols = sortOn (negate . Text.length)
      [ "->", "=>", "==", "!=", "<=", ">="
      , "@", "(", ")", "{", "}", ".", ",", ":", ";"
      , "[", "]", "|", "+", "-", "*", "=", "<", ">"
      ]

currentPoint :: Parser SourcePoint
currentPoint = do
  offset <- MP.getOffset
  position <- MP.getSourcePos
  pure SourcePoint
    { sourcePointFile = Text.pack (MP.sourceName position)
    , sourcePointLine = MP.unPos (MP.sourceLine position)
    , sourcePointColumn = MP.unPos (MP.sourceColumn position)
    , sourcePointOffset = offset
    }

diagnosticFromBundle :: MP.ParseErrorBundle Text Void -> GrammarV1LexDiagnostic
diagnosticFromBundle bundle =
  let firstError = NonEmpty.head (MP.bundleErrors bundle)
      offset = MP.errorOffset firstError
      (_, reachedState) = MP.reachOffset offset (MP.bundlePosState bundle)
      position = MP.pstateSourcePos reachedState
  in GrammarV1LexDiagnostic
      { grammarV1LexDiagnosticPoint = SourcePoint
          { sourcePointFile = Text.pack (MP.sourceName position)
          , sourcePointLine = MP.unPos (MP.sourceLine position)
          , sourcePointColumn = MP.unPos (MP.sourceColumn position)
          , sourcePointOffset = offset
          }
      , grammarV1LexDiagnosticMessage = Text.pack (MP.parseErrorTextPretty firstError)
      }
