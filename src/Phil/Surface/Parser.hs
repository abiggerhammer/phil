{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Parser
  ( ParseDiagnostic (..)
  , parseSurfaceFile
  , parseSurfaceExpression
  , parseSurfaceType
  , parseSurfaceProposition
  ) where

import Control.Applicative (empty, optional)
import Control.Monad (void)
import Data.Char (isDigit)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void)
import Phil.Surface.Syntax
import qualified Text.Megaparsec as MP
import Text.Megaparsec ((<|>))
import qualified Text.Megaparsec.Char as MPC
import qualified Text.Megaparsec.Char.Lexer as Lexer

type Parser = MP.Parsec Void Text

data ParseDiagnostic = ParseDiagnostic
  { parseDiagnosticPoint :: SourcePoint
  , parseDiagnosticMessage :: Text
  }
  deriving (Eq, Show)

parseSurfaceFile :: Text -> Text -> Either ParseDiagnostic SurfaceFile
parseSurfaceFile source = runSurfaceParser source $ do
  components <- MP.some pComponent
  pure (SurfaceFile components)

parseSurfaceExpression :: Text -> Text -> Either ParseDiagnostic (Located SurfaceExpression)
parseSurfaceExpression source = runSurfaceParser source pExpression

parseSurfaceType :: Text -> Text -> Either ParseDiagnostic (Located SurfaceType)
parseSurfaceType source = runSurfaceParser source pType

parseSurfaceProposition :: Text -> Text -> Either ParseDiagnostic (Located SurfaceProposition)
parseSurfaceProposition source = runSurfaceParser source pProposition

runSurfaceParser :: Text -> Parser a -> Text -> Either ParseDiagnostic a
runSurfaceParser source parser input =
  case MP.runParser (spaceConsumer *> parser <* MP.eof) (Text.unpack source) input of
    Right value -> Right value
    Left bundle -> Left (diagnosticFromBundle bundle)

diagnosticFromBundle :: MP.ParseErrorBundle Text Void -> ParseDiagnostic
diagnosticFromBundle bundle =
  let firstError = NonEmpty.head (MP.bundleErrors bundle)
      offset = MP.errorOffset firstError
      (_, reachedState) = MP.reachOffset offset (MP.bundlePosState bundle)
      position = MP.pstateSourcePos reachedState
  in ParseDiagnostic
      { parseDiagnosticPoint = sourcePoint offset position
      , parseDiagnosticMessage = Text.pack (MP.parseErrorTextPretty firstError)
      }

spaceConsumer :: Parser ()
spaceConsumer = Lexer.space MPC.space1 (Lexer.skipLineComment "//") empty

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaceConsumer

parens :: Parser a -> Parser a
parens = MP.between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = MP.between (symbol "[") (symbol "]")

reservedWords :: Set.Set Text
reservedWords = Set.fromList
  [ "component"
  , "provides"
  , "let"
  , "return"
  , "construct"
  , "receive"
  , "on"
  , "receive_frame"
  , "recognize"
  , "from"
  , "validate"
  , "at"
  , "send"
  , "send_exact"
  , "receive_exact"
  , "select"
  , "using"
  , "commit_receive"
  , "borrow"
  , "as"
  , "decide"
  , "offer"
  , "fail"
  , "close"
  , "release"
  , "accept"
  , "prove"
  , "or"
  , "reject"
  , "and"
  , "not"
  , "true"
  , "false"
  , "unit"
  ]

identifierStart :: Parser Char
identifierStart = MPC.letterChar <|> MPC.char '_'

identifierContinue :: Parser Char
identifierContinue = MPC.alphaNumChar <|> MPC.char '_' <|> MPC.char '\''

identifierText :: Parser Text
identifierText = Text.pack <$> ((:) <$> identifierStart <*> MP.many identifierContinue)

identifier :: Parser Text
identifier = lexeme . MP.try $ do
  name <- identifierText
  if Set.member name reservedWords
    then fail ("reserved word " ++ Text.unpack name ++ " cannot be used as an identifier here")
    else pure name

rawIdentifier :: Parser Text
rawIdentifier = lexeme identifierText

keyword :: Text -> Parser ()
keyword word = lexeme . MP.try $ void (MP.chunk word <* MP.notFollowedBy identifierContinue)

currentPoint :: Parser SourcePoint
currentPoint = do
  offset <- MP.getOffset
  position <- MP.getSourcePos
  pure (sourcePoint offset position)

sourcePoint :: Int -> MP.SourcePos -> SourcePoint
sourcePoint offset position = SourcePoint
  { sourcePointFile = Text.pack (MP.sourceName position)
  , sourcePointLine = MP.unPos (MP.sourceLine position)
  , sourcePointColumn = MP.unPos (MP.sourceColumn position)
  , sourcePointOffset = offset
  }

locatedParser :: Parser a -> Parser (Located a)
locatedParser parser = do
  start <- currentPoint
  value <- parser
  end <- currentPoint
  pure (Located (SourceSpan start end) value)

spanThrough :: Located a -> Located b -> SourceSpan
spanThrough left right = SourceSpan
  (sourceSpanStart (locatedSpan left))
  (sourceSpanEnd (locatedSpan right))

spanToPoint :: Located a -> SourcePoint -> SourceSpan
spanToPoint value end = SourceSpan (sourceSpanStart (locatedSpan value)) end

pComponent :: Parser (Located Component)
pComponent = locatedParser $ do
  keyword "component"
  name <- identifier
  parameters <- optional (parens (pParameter `MP.sepBy` symbol ","))
  provides <- optional (keyword "provides" *> pType)
  body <- pBlock
  pure Component
    { componentName = name
    , componentParameters = maybe [] id parameters
    , componentProvides = provides
    , componentBody = body
    }

pParameter :: Parser (Located Parameter)
pParameter = locatedParser $ do
  name <- identifier
  ty <- optional (symbol ":" *> pType)
  pure (Parameter name ty)

pBlock :: Parser (Located Block)
pBlock = locatedParser $ do
  void (symbol "{")
  statements <- MP.manyTill pStatement (symbol "}")
  pure (Block statements)

pStatement :: Parser (Located Statement)
pStatement = locatedParser (MP.choice [MP.try pLetStatement, MP.try pReturnStatement, pExpressionStatement])

pLetStatement :: Parser Statement
pLetStatement = do
  keyword "let"
  pattern' <- pPattern
  void (symbol "=")
  expression <- pExpression
  pure (LetStatement pattern' expression)

pReturnStatement :: Parser Statement
pReturnStatement = do
  keyword "return"
  ReturnStatement <$> pExpression

pExpressionStatement :: Parser Statement
pExpressionStatement = ExpressionStatement <$> pExpression

pPattern :: Parser (Located Pattern)
pPattern = locatedParser (MP.try pTuplePattern <|> (BindPattern <$> identifier))

pTuplePattern :: Parser Pattern
pTuplePattern = do
  patterns <- parens (pPattern `MP.sepBy1` symbol ",")
  if length patterns < 2
    then fail "tuple binding patterns require at least two elements"
    else pure (TuplePattern patterns)

pType :: Parser (Located SurfaceType)
pType = locatedParser $ do
  name <- rawIdentifier
  case parseUIntName name of
    Just width -> pure (SurfaceUIntType width)
    Nothing -> case name of
      "Unit" -> pure SurfaceUnitType
      "Bool" -> pure SurfaceBoolType
      "Bytes" -> SurfaceBytesType <$> brackets pExpression
      "Frame" -> SurfaceFrameType <$> brackets rawIdentifier
      "Proof" -> SurfaceProofType <$> brackets pProposition
      "Validated" -> brackets $ do
        claim <- rawIdentifier
        void (symbol ",")
        context <- pExpression
        void (symbol ",")
        subject <- pExpression
        pure (SurfaceValidatedType claim context subject)
      _ -> do
        arguments <- optional (brackets (pExpression `MP.sepBy` symbol ","))
        pure (SurfaceNamedType name (maybe [] id arguments))

parseUIntName :: Text -> Maybe Int
parseUIntName name = do
  digits <- Text.stripPrefix "U" name
  if Text.null digits || not (Text.all isDigit digits)
    then Nothing
    else Just (read (Text.unpack digits))

pExpression :: Parser (Located SurfaceExpression)
pExpression = do
  base <- pExpressionNoFallback
  MP.option base (pFallbackSuffix base)

pFallbackSuffix :: Located SurfaceExpression -> Parser (Located SurfaceExpression)
pFallbackSuffix base = do
  keyword "or"
  fallback <-
    (FailFallback <$> (keyword "fail" *> rawIdentifier))
      <|> (RejectFallback <$> (keyword "reject" *> pExpressionNoFallback))
  end <- currentPoint
  pure (Located (spanToPoint base end) (FallbackExpression base fallback))

pExpressionNoFallback :: Parser (Located SurfaceExpression)
pExpressionNoFallback = pAddSubtract

pAddSubtract :: Parser (Located SurfaceExpression)
pAddSubtract = chainLeft pMultiply addOperator
  where
    addOperator =
      (symbol "+" *> pure Add)
        <|> (symbol "-" *> pure Subtract)

pMultiply :: Parser (Located SurfaceExpression)
pMultiply = chainLeft pPostfix (symbol "*" *> pure Multiply)

chainLeft
  :: Parser (Located SurfaceExpression)
  -> Parser BinaryOperator
  -> Parser (Located SurfaceExpression)
chainLeft operand operator = do
  first <- operand
  go first
  where
    go left =
      (do
          operation <- operator
          right <- operand
          let combined = Located
                (spanThrough left right)
                (BinaryExpression operation left right)
          go combined)
        <|> pure left

pPostfix :: Parser (Located SurfaceExpression)
pPostfix = pPrimary >>= addFields
  where
    addFields base =
      (do
          void (symbol ".")
          field <- rawIdentifier
          end <- currentPoint
          addFields (Located (spanToPoint base end) (FieldExpression base field)))
        <|> pure base

pPrimary :: Parser (Located SurfaceExpression)
pPrimary = locatedParser $ MP.choice
  [ MP.try pConstructExpression
  , MP.try pBorrowExpression
  , MP.try pDecideExpression
  , MP.try pOfferExpression
  , MP.try pReceiveFrameExpression
  , MP.try pReceiveExactExpression
  , MP.try pReceiveExpression
  , MP.try pRecognizeExpression
  , MP.try pValidateExpression
  , MP.try pSendExactExpression
  , MP.try pSendExpression
  , MP.try pSelectExpression
  , MP.try pCommitReceiveExpression
  , MP.try pFailExpression
  , MP.try pCloseExpression
  , MP.try pReleaseExpression
  , MP.try pAcceptExpression
  , MP.try pProveExpression
  , MP.try pParenthesizedExpression
  , MP.try pBooleanOrUnitExpression
  , MP.try pIntegerExpression
  , pCallOrVariableExpression
  ]

pConstructExpression :: Parser SurfaceExpression
pConstructExpression = do
  keyword "construct"
  constructor <- rawIdentifier
  fields <- MP.between (symbol "{") (symbol "}") (pFieldAssignment `MP.sepEndBy` symbol ",")
  pure (ConstructExpression constructor fields)
  where
    pFieldAssignment = do
      field <- rawIdentifier
      void (symbol "=")
      value <- pExpression
      pure (field, value)

pBorrowExpression :: Parser SurfaceExpression
pBorrowExpression = do
  keyword "borrow"
  owner <- pExpressionNoFallback
  keyword "as"
  view <- identifier
  body <- pBlock
  pure (BorrowExpression owner view body)

pDecideExpression :: Parser SurfaceExpression
pDecideExpression = do
  keyword "decide"
  scrutinee <- pExpressionNoFallback
  arms <- pCaseArms
  pure (DecideExpression scrutinee arms)

pOfferExpression :: Parser SurfaceExpression
pOfferExpression = do
  keyword "offer"
  endpoint <- pExpressionNoFallback
  arms <- pCaseArms
  pure (OfferExpression endpoint arms)

pCaseArms :: Parser [Located CaseArm]
pCaseArms = MP.between (symbol "{") (symbol "}") (MP.many pCaseArm)

pCaseArm :: Parser (Located CaseArm)
pCaseArm = locatedParser $ do
  pattern' <- pCasePattern
  void (symbol "=>")
  body <- pBlock <|> pSingleStatementBlock
  pure (CaseArm pattern' body)

pSingleStatementBlock :: Parser (Located Block)
pSingleStatementBlock = do
  statement <- pStatement
  pure (Located (locatedSpan statement) (Block [statement]))

pCasePattern :: Parser CasePattern
pCasePattern = do
  label <- rawIdentifier
  binders <- optional (parens (identifier `MP.sepBy` symbol ","))
  pure (CasePattern label (maybe [] id binders))

pReceiveFrameExpression :: Parser SurfaceExpression
pReceiveFrameExpression = do
  keyword "receive_frame"
  ReceiveFrameExpression <$> parens pExpression

pReceiveExactExpression :: Parser SurfaceExpression
pReceiveExactExpression = do
  keyword "receive_exact"
  count <- pExpressionNoFallback
  keyword "on"
  endpoint <- pExpressionNoFallback
  evidence <- optional (keyword "using" *> pExpressionNoFallback)
  pure (ReceiveExactExpression count endpoint evidence)

pReceiveExpression :: Parser SurfaceExpression
pReceiveExpression = do
  keyword "receive"
  messageType <- pType
  keyword "on"
  endpoint <- pExpressionNoFallback
  pure (ReceiveExpression messageType endpoint)

pRecognizeExpression :: Parser SurfaceExpression
pRecognizeExpression = do
  keyword "recognize"
  grammar <- rawIdentifier
  keyword "from"
  raw <- pExpressionNoFallback
  pure (RecognizeExpression grammar raw)

pValidateExpression :: Parser SurfaceExpression
pValidateExpression = do
  keyword "validate"
  claim <- rawIdentifier
  context <- optional (keyword "at" *> pExpressionNoFallback)
  keyword "on"
  subject <- pExpressionNoFallback
  pure (ValidateExpression claim context subject)

pSendExactExpression :: Parser SurfaceExpression
pSendExactExpression = do
  keyword "send_exact"
  value <- pExpressionNoFallback
  keyword "on"
  endpoint <- pExpressionNoFallback
  pure (SendExactExpression value endpoint)

pSendExpression :: Parser SurfaceExpression
pSendExpression = do
  keyword "send"
  value <- pExpressionNoFallback
  keyword "on"
  endpoint <- pExpressionNoFallback
  pure (SendExpression value endpoint)

pSelectExpression :: Parser SurfaceExpression
pSelectExpression = do
  keyword "select"
  branch <- pBranchValue
  keyword "on"
  endpoint <- pExpressionNoFallback
  evidence <- optional (keyword "using" *> pExpressionNoFallback)
  pure (SelectExpression branch endpoint evidence)

pBranchValue :: Parser BranchValue
pBranchValue = do
  label <- rawIdentifier
  arguments <- optional (parens (pExpression `MP.sepBy` symbol ","))
  pure (BranchValue label (maybe [] id arguments))

pCommitReceiveExpression :: Parser SurfaceExpression
pCommitReceiveExpression = do
  keyword "commit_receive"
  pending <- pExpressionNoFallback
  keyword "using"
  evidence <- pExpressionNoFallback
  pure (CommitReceiveExpression pending evidence)

pFailExpression :: Parser SurfaceExpression
pFailExpression = do
  keyword "fail"
  target <- pFailureTarget
  keyword "on"
  resource <- pExpressionNoFallback
  pure (FailExpression target resource)

pFailureTarget :: Parser FailureTarget
pFailureTarget = do
  failureClass <- rawIdentifier
  arguments <- optional (parens (pExpression `MP.sepBy` symbol ","))
  pure (FailureTarget failureClass (maybe [] id arguments))

pCloseExpression :: Parser SurfaceExpression
pCloseExpression = keyword "close" *> (CloseExpression <$> pExpressionNoFallback)

pReleaseExpression :: Parser SurfaceExpression
pReleaseExpression = keyword "release" *> (ReleaseExpression <$> pExpressionNoFallback)

pAcceptExpression :: Parser SurfaceExpression
pAcceptExpression = do
  keyword "accept"
  value <- pExpressionNoFallback
  keyword "as"
  AcceptExpression value <$> pType

pProveExpression :: Parser SurfaceExpression
pProveExpression = keyword "prove" *> (ProveExpression <$> pProposition)

pParenthesizedExpression :: Parser SurfaceExpression
pParenthesizedExpression = do
  values <- parens (pExpression `MP.sepBy` symbol ",")
  case values of
    [] -> pure UnitExpression
    [single] -> pure (locatedValue single)
    _ -> pure (TupleExpression values)

pBooleanOrUnitExpression :: Parser SurfaceExpression
pBooleanOrUnitExpression =
  (keyword "true" *> pure (BooleanExpression True))
    <|> (keyword "false" *> pure (BooleanExpression False))
    <|> (keyword "unit" *> pure UnitExpression)

pIntegerExpression :: Parser SurfaceExpression
pIntegerExpression = IntegerExpression <$> lexeme Lexer.decimal

pCallOrVariableExpression :: Parser SurfaceExpression
pCallOrVariableExpression = do
  name <- identifier
  arguments <- optional (parens (pExpression `MP.sepBy` symbol ","))
  pure $ case arguments of
    Nothing -> VariableExpression name
    Just values -> CallExpression name values

pProposition :: Parser (Located SurfaceProposition)
pProposition = pPropositionOr

pPropositionOr :: Parser (Located SurfaceProposition)
pPropositionOr = chainProposition pPropositionAnd "or" PropositionDisjunction

pPropositionAnd :: Parser (Located SurfaceProposition)
pPropositionAnd = chainProposition pPropositionNot "and" PropositionConjunction

chainProposition
  :: Parser (Located SurfaceProposition)
  -> Text
  -> (Located SurfaceProposition -> Located SurfaceProposition -> SurfaceProposition)
  -> Parser (Located SurfaceProposition)
chainProposition operand operator constructor = do
  first <- operand
  go first
  where
    go left =
      (do
          keyword operator
          right <- operand
          go (Located (spanThrough left right) (constructor left right)))
        <|> pure left

pPropositionNot :: Parser (Located SurfaceProposition)
pPropositionNot =
  locatedParser (keyword "not" *> (PropositionNegation <$> pPropositionNot))
    <|> pPropositionAtom

pPropositionAtom :: Parser (Located SurfaceProposition)
pPropositionAtom = locatedParser $ MP.choice
  [ MP.try pPropositionComparison
  , MP.try pPropositionParenthesized
  , MP.try pPropositionTruth
  , pPropositionClaim
  ]

pPropositionComparison :: Parser SurfaceProposition
pPropositionComparison = do
  left <- pExpressionNoFallback
  constructor <- MP.choice
    [ symbol "==" *> pure PropositionEqual
    , symbol "!=" *> pure PropositionNotEqual
    , symbol "<=" *> pure PropositionLessEqual
    , symbol ">=" *> pure PropositionGreaterEqual
    , symbol "<" *> pure PropositionLessThan
    , symbol ">" *> pure PropositionGreaterThan
    ]
  right <- pExpressionNoFallback
  pure (constructor left right)

pPropositionParenthesized :: Parser SurfaceProposition
pPropositionParenthesized = locatedValue <$> parens pProposition

pPropositionTruth :: Parser SurfaceProposition
pPropositionTruth =
  (keyword "true" *> pure PropositionTrue)
    <|> (keyword "false" *> pure PropositionFalse)

pPropositionClaim :: Parser SurfaceProposition
pPropositionClaim = do
  claim <- identifier
  arguments <- parens (pExpression `MP.sepBy` symbol ",")
  pure (PropositionAtom claim arguments)
