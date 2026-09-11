{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ReferenceAstFixedCommands
  ( GrammarV1ReferenceFixedCommandError (..)
  , GrammarV1ReferenceFixedCommand (..)
  , grammarV1ProductionFixedCommand
  , grammarV1ReferenceFixedCommand
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstExpressionCore
  ( GrammarV1ReferenceExpressionCore
  , GrammarV1ReferenceExpressionCoreError
  , grammarV1ProductionExpressionCore
  , grammarV1ReferenceExpressionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore
  , GrammarV1ReferencePropositionError
  , grammarV1ProductionPropositionCore
  , grammarV1ReferencePropositionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticReferenceError
  , GrammarV1ReferenceStaticReferenceSpine
  , grammarV1ProductionStaticReferenceSpine
  , grammarV1ReferenceStaticReferenceSpine
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceTypePayload
  , GrammarV1ReferenceTypePayloadError
  , grammarV1ProductionTypePayload
  , grammarV1ReferenceTypePayload
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  )
import Phil.Surface.Syntax (Located (..))

newtype GrammarV1ReferenceFixedCommandError =
  GrammarV1ReferenceFixedCommandError Text
  deriving (Eq, Show)

data GrammarV1ReferenceFixedCommand
  = GrammarV1ReferenceReceiveFrame GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceReceiveExact
      GrammarV1ReferenceExpressionCore
      (Maybe GrammarV1ReferenceExpressionCore)
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceReceive
      GrammarV1ReferenceTypePayload
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceRecognize
      GrammarV1ReferenceStaticReferenceSpine
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceValidate
      GrammarV1ReferenceStaticReferenceSpine
      (Maybe GrammarV1ReferenceExpressionCore)
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceSendExact
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceSend
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceCommitReceive
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceReject GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceClose GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceRelease GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceConvert
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceTransport
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceTypePayload
      GrammarV1ReferenceExpressionCore
  | GrammarV1ReferenceAccept
      GrammarV1ReferenceExpressionCore
      GrammarV1ReferenceTypePayload
  | GrammarV1ReferenceProve GrammarV1ReferencePropositionCore
  deriving (Eq, Show)

grammarV1ProductionFixedCommand
  :: GrammarV1Expression
  -> Maybe GrammarV1ReferenceFixedCommand
grammarV1ProductionFixedCommand expression = case expression of
  GrammarV1ReceiveFrameExpression source ->
    Just (GrammarV1ReferenceReceiveFrame (productionExpression source))
  GrammarV1ReceiveExactExpression amount endpoint evidence ->
    Just (GrammarV1ReferenceReceiveExact
      (productionExpression amount)
      (fmap productionExpression evidence)
      (productionExpression endpoint))
  GrammarV1ReceiveExpression resultType endpoint ->
    Just (GrammarV1ReferenceReceive
      (grammarV1ProductionTypePayload (locatedValue resultType))
      (productionExpression endpoint))
  GrammarV1RecognizeExpression recognizer source ->
    Just (GrammarV1ReferenceRecognize
      (grammarV1ProductionStaticReferenceSpine (locatedValue recognizer))
      (productionExpression source))
  GrammarV1ValidateExpression validator position endpoint ->
    Just (GrammarV1ReferenceValidate
      (grammarV1ProductionStaticReferenceSpine (locatedValue validator))
      (fmap productionExpression position)
      (productionExpression endpoint))
  GrammarV1SendExactExpression value endpoint ->
    Just (GrammarV1ReferenceSendExact
      (productionExpression value)
      (productionExpression endpoint))
  GrammarV1SendExpression value endpoint ->
    Just (GrammarV1ReferenceSend
      (productionExpression value)
      (productionExpression endpoint))
  GrammarV1CommitReceiveExpression source evidence ->
    Just (GrammarV1ReferenceCommitReceive
      (productionExpression source)
      (productionExpression evidence))
  GrammarV1RejectExpression value ->
    Just (GrammarV1ReferenceReject (productionExpression value))
  GrammarV1CloseExpression endpoint ->
    Just (GrammarV1ReferenceClose (productionExpression endpoint))
  GrammarV1ReleaseExpression value ->
    Just (GrammarV1ReferenceRelease (productionExpression value))
  GrammarV1ConvertExpression value target ->
    Just (GrammarV1ReferenceConvert
      (productionExpression value)
      (grammarV1ProductionTypePayload (locatedValue target)))
  GrammarV1TransportExpression value target evidence ->
    Just (GrammarV1ReferenceTransport
      (productionExpression value)
      (grammarV1ProductionTypePayload (locatedValue target))
      (productionExpression evidence))
  GrammarV1AcceptExpression value target ->
    Just (GrammarV1ReferenceAccept
      (productionExpression value)
      (grammarV1ProductionTypePayload (locatedValue target)))
  GrammarV1ProveExpression proposition ->
    Just (GrammarV1ReferenceProve
      (grammarV1ProductionPropositionCore (locatedValue proposition)))
  _ -> Nothing
  where
    productionExpression = grammarV1ProductionExpressionCore . locatedValue

grammarV1ReferenceFixedCommand
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError (Maybe GrammarV1ReferenceFixedCommand)
grammarV1ReferenceFixedCommand tree = do
  body <- expectNonterminal "command_expression" tree
  case body of
    GrammarV1ReferenceAlternative index selected -> case index of
      9 -> Just <$> parseReceiveFrame selected
      10 -> Just <$> parseReceiveExact selected
      11 -> Just <$> parseReceive selected
      12 -> Just <$> parseRecognize selected
      13 -> Just <$> parseValidate selected
      14 -> Just <$> parseSendExact selected
      15 -> Just <$> parseSend selected
      18 -> Just <$> parseCommitReceive selected
      19 -> Just <$> parseReject selected
      21 -> Just <$> parseClose selected
      22 -> Just <$> parseRelease selected
      23 -> Just <$> parseConvert selected
      24 -> Just <$> parseTransport selected
      25 -> Just <$> parseAccept selected
      27 -> Just <$> parseProve selected
      _ | index >= 0 && index <= 27 -> pure Nothing
        | otherwise -> failFixed
            ("command_expression alternative out of range: " <> showText index)
    _ -> failFixed "command_expression body is not an alternative node"

parseReceiveFrame, parseReceiveExact, parseReceive, parseRecognize, parseValidate,
  parseSendExact, parseSend, parseCommitReceive, parseReject, parseClose,
  parseRelease, parseConvert, parseTransport, parseAccept, parseProve
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError GrammarV1ReferenceFixedCommand

parseReceiveFrame tree = do
  fields <- namedSequence "receive_frame_expression" tree
  case fields of
    [keyword, openParen, sourceTree, closeParen] -> do
      expectLiteral "receive_frame" keyword
      expectLiteral "(" openParen
      source <- mapExpressionError (grammarV1ReferenceExpressionCore sourceTree)
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceReceiveFrame source)
    _ -> failFixed "receive_frame_expression body is not a four-item sequence"

parseReceiveExact tree = do
  fields <- namedSequence "receive_exact_expression" tree
  case fields of
    [keyword, amountTree, optionalUsing, onKeyword, endpointTree] -> do
      expectLiteral "receive_exact" keyword
      amount <- parseBase amountTree
      evidence <- parseOptionalKeywordBase "using" optionalUsing
      expectLiteral "on" onKeyword
      endpoint <- parseBase endpointTree
      pure (GrammarV1ReferenceReceiveExact amount evidence endpoint)
    _ -> failFixed "receive_exact_expression body is not a five-item sequence"

parseReceive tree = do
  fields <- namedSequence "receive_expression" tree
  case fields of
    [keyword, typeTree, onKeyword, endpointTree] -> do
      expectLiteral "receive" keyword
      resultType <- mapTypeError (grammarV1ReferenceTypePayload typeTree)
      expectLiteral "on" onKeyword
      endpoint <- parseBase endpointTree
      pure (GrammarV1ReferenceReceive resultType endpoint)
    _ -> failFixed "receive_expression body is not a four-item sequence"

parseRecognize tree = do
  fields <- namedSequence "recognize_expression" tree
  case fields of
    [keyword, recognizerTree, fromKeyword, sourceTree] -> do
      expectLiteral "recognize" keyword
      recognizer <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine recognizerTree)
      expectLiteral "from" fromKeyword
      source <- parseBase sourceTree
      pure (GrammarV1ReferenceRecognize recognizer source)
    _ -> failFixed "recognize_expression body is not a four-item sequence"

parseValidate tree = do
  fields <- namedSequence "validate_expression" tree
  case fields of
    [keyword, validatorTree, optionalAt, onKeyword, endpointTree] -> do
      expectLiteral "validate" keyword
      validator <- mapStaticReferenceError
        (grammarV1ReferenceStaticReferenceSpine validatorTree)
      position <- parseOptionalKeywordBase "at" optionalAt
      expectLiteral "on" onKeyword
      endpoint <- parseBase endpointTree
      pure (GrammarV1ReferenceValidate validator position endpoint)
    _ -> failFixed "validate_expression body is not a five-item sequence"

parseSendExact = parseBinaryBaseCommand
  "send_exact_expression" "send_exact" "on" GrammarV1ReferenceSendExact
parseSend = parseBinaryBaseCommand
  "send_expression" "send" "on" GrammarV1ReferenceSend
parseCommitReceive = parseBinaryBaseCommand
  "commit_receive_expression" "commit_receive" "using" GrammarV1ReferenceCommitReceive
parseReject = parseUnaryBaseCommand
  "reject_expression" "reject" GrammarV1ReferenceReject
parseClose = parseUnaryBaseCommand
  "close_expression" "close" GrammarV1ReferenceClose
parseRelease = parseUnaryBaseCommand
  "release_expression" "release" GrammarV1ReferenceRelease

parseConvert tree = do
  fields <- namedSequence "convert_expression" tree
  case fields of
    [keyword, valueTree, toKeyword, targetTree] -> do
      expectLiteral "convert" keyword
      value <- mapExpressionError (grammarV1ReferenceExpressionCore valueTree)
      expectLiteral "to" toKeyword
      target <- mapTypeError (grammarV1ReferenceTypePayload targetTree)
      pure (GrammarV1ReferenceConvert value target)
    _ -> failFixed "convert_expression body is not a four-item sequence"

parseTransport tree = do
  fields <- namedSequence "transport_expression" tree
  case fields of
    [keyword, valueTree, toKeyword, targetTree, usingKeyword, evidenceTree] -> do
      expectLiteral "transport" keyword
      value <- parseBase valueTree
      expectLiteral "to" toKeyword
      target <- mapTypeError (grammarV1ReferenceTypePayload targetTree)
      expectLiteral "using" usingKeyword
      evidence <- parseBase evidenceTree
      pure (GrammarV1ReferenceTransport value target evidence)
    _ -> failFixed "transport_expression body is not a six-item sequence"

parseAccept tree = do
  fields <- namedSequence "accept_expression" tree
  case fields of
    [keyword, valueTree, asKeyword, targetTree] -> do
      expectLiteral "accept" keyword
      value <- parseBase valueTree
      expectLiteral "as" asKeyword
      target <- mapTypeError (grammarV1ReferenceTypePayload targetTree)
      pure (GrammarV1ReferenceAccept value target)
    _ -> failFixed "accept_expression body is not a four-item sequence"

parseProve tree = do
  fields <- namedSequence "prove_expression" tree
  case fields of
    [keyword, openParen, propositionTree, closeParen] -> do
      expectLiteral "prove" keyword
      expectLiteral "(" openParen
      proposition <- mapPropositionError
        (grammarV1ReferencePropositionCore propositionTree)
      expectLiteral ")" closeParen
      pure (GrammarV1ReferenceProve proposition)
    _ -> failFixed "prove_expression body is not a four-item sequence"

parseBinaryBaseCommand
  :: Text
  -> Text
  -> Text
  -> (GrammarV1ReferenceExpressionCore
      -> GrammarV1ReferenceExpressionCore
      -> GrammarV1ReferenceFixedCommand)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError GrammarV1ReferenceFixedCommand
parseBinaryBaseCommand nonterminal keyword separator constructor tree = do
  fields <- namedSequence nonterminal tree
  case fields of
    [keywordTree, leftTree, separatorTree, rightTree] -> do
      expectLiteral keyword keywordTree
      left <- parseBase leftTree
      expectLiteral separator separatorTree
      right <- parseBase rightTree
      pure (constructor left right)
    _ -> failFixed (nonterminal <> " body is not a four-item sequence")

parseUnaryBaseCommand
  :: Text
  -> Text
  -> (GrammarV1ReferenceExpressionCore -> GrammarV1ReferenceFixedCommand)
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError GrammarV1ReferenceFixedCommand
parseUnaryBaseCommand nonterminal keyword constructor tree = do
  fields <- namedSequence nonterminal tree
  case fields of
    [keywordTree, valueTree] -> do
      expectLiteral keyword keywordTree
      constructor <$> parseBase valueTree
    _ -> failFixed (nonterminal <> " body is not a two-item sequence")

parseOptionalKeywordBase
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError (Maybe GrammarV1ReferenceExpressionCore)
parseOptionalKeywordBase keyword tree = case tree of
  GrammarV1ReferenceOptionalNone -> pure Nothing
  GrammarV1ReferenceOptionalSome valueTree -> do
    fields <- expectSequence (keyword <> " optional payload") valueTree
    case fields of
      [keywordTree, baseTree] -> do
        expectLiteral keyword keywordTree
        Just <$> parseBase baseTree
      _ -> failFixed (keyword <> " optional payload is not a two-item sequence")
  _ -> failFixed (keyword <> " payload slot is not optional")

parseBase
  :: GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError GrammarV1ReferenceExpressionCore
parseBase baseTree =
  mapExpressionError
    (grammarV1ReferenceExpressionCore
      (GrammarV1ReferenceNonterminal "expression"
        (GrammarV1ReferenceSequence
          [baseTree, GrammarV1ReferenceOptionalNone])))

namedSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError [GrammarV1ReferenceParseTree]
namedSequence name tree = expectNonterminal name tree >>= expectSequence name

expectNonterminal
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError GrammarV1ReferenceParseTree
expectNonterminal expected tree = case tree of
  GrammarV1ReferenceNonterminal actual body
    | actual == expected -> pure body
    | otherwise -> failFixed
        ("expected nonterminal " <> expected <> ", got " <> actual)
  _ -> failFixed ("expected nonterminal " <> expected)

expectSequence
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError [GrammarV1ReferenceParseTree]
expectSequence label tree = case tree of
  GrammarV1ReferenceSequence values -> pure values
  _ -> failFixed (label <> " is not a sequence node")

expectLiteral
  :: Text
  -> GrammarV1ReferenceParseTree
  -> Either GrammarV1ReferenceFixedCommandError ()
expectLiteral expected tree = case tree of
  GrammarV1ReferenceLiteral actual
    | actual == expected -> pure ()
    | otherwise -> failFixed
        ("expected literal " <> expected <> ", got " <> actual)
  _ -> failFixed ("expected literal " <> expected)

mapExpressionError
  :: Either GrammarV1ReferenceExpressionCoreError a
  -> Either GrammarV1ReferenceFixedCommandError a
mapExpressionError = mapLeft
  (GrammarV1ReferenceFixedCommandError . Text.pack . show)

mapPropositionError
  :: Either GrammarV1ReferencePropositionError a
  -> Either GrammarV1ReferenceFixedCommandError a
mapPropositionError = mapLeft
  (GrammarV1ReferenceFixedCommandError . Text.pack . show)

mapStaticReferenceError
  :: Either GrammarV1ReferenceStaticReferenceError a
  -> Either GrammarV1ReferenceFixedCommandError a
mapStaticReferenceError = mapLeft
  (GrammarV1ReferenceFixedCommandError . Text.pack . show)

mapTypeError
  :: Either GrammarV1ReferenceTypePayloadError a
  -> Either GrammarV1ReferenceFixedCommandError a
mapTypeError = mapLeft
  (GrammarV1ReferenceFixedCommandError . Text.pack . show)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value

showText :: Show a => a -> Text
showText = Text.pack . show

failFixed :: Text -> Either GrammarV1ReferenceFixedCommandError a
failFixed = Left . GrammarV1ReferenceFixedCommandError
