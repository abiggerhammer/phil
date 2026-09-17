{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.ComponentRequestReplyOutput
  ( GrammarV1CheckedRequestReplyClient (..)
  , GrammarV1CheckedRequestReplyServer (..)
  , GrammarV1RequestReplyOutputError (..)
  , grammarV1CheckedRequestReplyClient
  , grammarV1CheckedRequestReplyServer
  ) where

import Data.Text (Text)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1Pattern (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  , grammarV1QualifiedNameParts
  , pattern GrammarV1StringExpression
  )
import Phil.Surface.GrammarV1.PatternBinderScope
  ( grammarV1BindPattern
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact source-binder carrier for INT-009 stage 2's client:
--
--     let awaiting = send payload on endpoint;
--     let (done, reply) = receive String on awaiting;
--     let writeDecision = console_write(reply);
--     close done;
data GrammarV1CheckedRequestReplyClient = GrammarV1CheckedRequestReplyClient
  { requestReplyClientPayload :: GrammarV1ResolvedBinder
  , requestReplyClientInitialEndpoint :: GrammarV1ResolvedBinder
  , requestReplyClientReplyEndpoint :: GrammarV1ResolvedBinder
  , requestReplyClientTerminalEndpoint :: GrammarV1ResolvedBinder
  , requestReplyClientReplyValue :: GrammarV1ResolvedBinder
  , requestReplyClientWriteDecision :: GrammarV1ResolvedBinder
  }
  deriving (Eq, Show)

-- | Exact source-binder carrier for the matching server:
--
--     let (replyEndpoint, request) = receive U8 on endpoint;
--     let done = send "pong" on replyEndpoint;
--     close done;
data GrammarV1CheckedRequestReplyServer = GrammarV1CheckedRequestReplyServer
  { requestReplyServerInitialEndpoint :: GrammarV1ResolvedBinder
  , requestReplyServerReplyEndpoint :: GrammarV1ResolvedBinder
  , requestReplyServerRequestValue :: GrammarV1ResolvedBinder
  , requestReplyServerTerminalEndpoint :: GrammarV1ResolvedBinder
  , requestReplyServerReplyText :: Text
  }
  deriving (Eq, Show)

data GrammarV1RequestReplyOutputError
  = GrammarV1RequestReplyBinderError GrammarV1BinderScopeError
  | GrammarV1RequestReplyOperandNotLocal Text
  | GrammarV1RequestReplyOperandNotParameter Text GrammarV1ResolvedBinder
  | GrammarV1RequestReplyPatternShape Text
  | GrammarV1RequestReplyEndpointMismatch
      Text
      GrammarV1ResolvedBinder
      GrammarV1ResolvedBinder
  | GrammarV1RequestReplyReceiveTypeMismatch GrammarV1Type GrammarV1Type
  | GrammarV1RequestReplyOutputPrimitiveMismatch
  | GrammarV1RequestReplyOutputArgumentMismatch
      GrammarV1ResolvedBinder
      GrammarV1ResolvedBinder
  | GrammarV1RequestReplyReplyLiteralRequired
  deriving (Eq, Show)

-- | Claim competence only for the bounded Stage-2 client shape. Once that
-- shape matches, every local use must resolve to the exact declaration-rooted
-- binder produced by the previous operation.
grammarV1CheckedRequestReplyClient
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1RequestReplyOutputError
        GrammarV1CheckedRequestReplyClient)
grammarV1CheckedRequestReplyClient declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement sendPattern sendSource)
      , Located _ (GrammarV1LetStatement receivePattern receiveSource)
      , Located _ (GrammarV1LetStatement writePattern writeSource)
      , Located _ (GrammarV1ExpressionStatement closeSource)
      ] ->
        case
          ( locatedValue sendSource
          , locatedValue receiveSource
          , locatedValue writeSource
          , locatedValue closeSource
          ) of
          ( GrammarV1SendExpression payloadSource initialEndpointSource
            , GrammarV1ReceiveExpression receiveType replyEndpointSource
            , GrammarV1NameExpression writeReference [writeArgumentSource]
            , GrammarV1CloseExpression terminalEndpointSource
            ) -> Just $ do
              (maybeParameters, parameterScope) <- mapLeft
                GrammarV1RequestReplyBinderError
                (grammarV1ComponentParameterScope declarationKey component)
              let parameters = maybe [] id maybeParameters
              payload <- requireLocal "send payload" parameterScope payloadSource
              initialEndpoint <- requireLocal
                "send endpoint"
                parameterScope
                initialEndpointSource
              requireParameter "send payload" parameters payload
              requireParameter "send endpoint" parameters initialEndpoint

              (replyEndpoint, afterSend) <- bindIdentifier
                "send successor"
                sendPattern
                parameterScope
              receiveEndpoint <- requireLocal
                "receive endpoint"
                afterSend
                replyEndpointSource
              requireSameBinder
                "send successor -> receive endpoint"
                replyEndpoint
                (grammarV1CheckedLocalValueBinder receiveEndpoint)
              requireType
                (GrammarV1UnsignedType "String")
                (locatedValue receiveType)

              (terminalEndpoint, replyValue, afterReceive) <- bindTuple2
                "receive result"
                receivePattern
                afterSend
              requireConsoleWrite writeReference
              writeArgument <- requireLocal
                "console_write argument"
                afterReceive
                writeArgumentSource
              let writeArgumentBinder = grammarV1CheckedLocalValueBinder writeArgument
              if grammarV1ResolvedBinderKey writeArgumentBinder
                  == grammarV1ResolvedBinderKey replyValue
                then Right ()
                else Left
                  (GrammarV1RequestReplyOutputArgumentMismatch
                    replyValue writeArgumentBinder)

              (writeDecision, afterWrite) <- bindIdentifier
                "console_write decision"
                writePattern
                afterReceive
              closeEndpoint <- requireLocal
                "close endpoint"
                afterWrite
                terminalEndpointSource
              requireSameBinder
                "receive terminal -> close endpoint"
                terminalEndpoint
                (grammarV1CheckedLocalValueBinder closeEndpoint)

              Right GrammarV1CheckedRequestReplyClient
                { requestReplyClientPayload = grammarV1CheckedLocalValueBinder payload
                , requestReplyClientInitialEndpoint =
                    grammarV1CheckedLocalValueBinder initialEndpoint
                , requestReplyClientReplyEndpoint = replyEndpoint
                , requestReplyClientTerminalEndpoint = terminalEndpoint
                , requestReplyClientReplyValue = replyValue
                , requestReplyClientWriteDecision = writeDecision
                }
          _ -> Nothing
    _ -> Nothing

-- | Claim competence only for the bounded Stage-2 server shape.
grammarV1CheckedRequestReplyServer
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1RequestReplyOutputError
        GrammarV1CheckedRequestReplyServer)
grammarV1CheckedRequestReplyServer declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement receivePattern receiveSource)
      , Located _ (GrammarV1LetStatement sendPattern sendSource)
      , Located _ (GrammarV1ExpressionStatement closeSource)
      ] ->
        case (locatedValue receiveSource, locatedValue sendSource, locatedValue closeSource) of
          ( GrammarV1ReceiveExpression receiveType initialEndpointSource
            , GrammarV1SendExpression replySource replyEndpointSource
            , GrammarV1CloseExpression terminalEndpointSource
            ) -> Just $ do
              (maybeParameters, parameterScope) <- mapLeft
                GrammarV1RequestReplyBinderError
                (grammarV1ComponentParameterScope declarationKey component)
              let parameters = maybe [] id maybeParameters
              initialEndpoint <- requireLocal
                "receive endpoint"
                parameterScope
                initialEndpointSource
              requireParameter "receive endpoint" parameters initialEndpoint
              requireType (GrammarV1UnsignedType "U8") (locatedValue receiveType)

              (replyEndpoint, requestValue, afterReceive) <- bindTuple2
                "receive result"
                receivePattern
                parameterScope
              sendEndpoint <- requireLocal
                "send endpoint"
                afterReceive
                replyEndpointSource
              requireSameBinder
                "receive successor -> send endpoint"
                replyEndpoint
                (grammarV1CheckedLocalValueBinder sendEndpoint)
              replyText <- case locatedValue replySource of
                GrammarV1StringExpression value -> Right value
                _ -> Left GrammarV1RequestReplyReplyLiteralRequired

              (terminalEndpoint, afterSend) <- bindIdentifier
                "send successor"
                sendPattern
                afterReceive
              closeEndpoint <- requireLocal
                "close endpoint"
                afterSend
                terminalEndpointSource
              requireSameBinder
                "send terminal -> close endpoint"
                terminalEndpoint
                (grammarV1CheckedLocalValueBinder closeEndpoint)

              Right GrammarV1CheckedRequestReplyServer
                { requestReplyServerInitialEndpoint =
                    grammarV1CheckedLocalValueBinder initialEndpoint
                , requestReplyServerReplyEndpoint = replyEndpoint
                , requestReplyServerRequestValue = requestValue
                , requestReplyServerTerminalEndpoint = terminalEndpoint
                , requestReplyServerReplyText = replyText
                }
          _ -> Nothing
    _ -> Nothing

requireConsoleWrite
  :: GrammarV1StaticReference
  -> Either GrammarV1RequestReplyOutputError ()
requireConsoleWrite reference
  | grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference)
      == ["console_write"]
    && null (grammarV1StaticReferenceArguments reference) = Right ()
  | otherwise = Left GrammarV1RequestReplyOutputPrimitiveMismatch

requireLocal
  :: Text
  -> GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Either GrammarV1RequestReplyOutputError GrammarV1CheckedLocalValueOccurrence
requireLocal role scope source =
  maybe
    (Left (GrammarV1RequestReplyOperandNotLocal role))
    Right
    (grammarV1CheckedLocalValueOccurrenceInScope scope source)

requireParameter
  :: Text
  -> [GrammarV1ResolvedBinder]
  -> GrammarV1CheckedLocalValueOccurrence
  -> Either GrammarV1RequestReplyOutputError ()
requireParameter role parameters occurrence =
  let binder = grammarV1CheckedLocalValueBinder occurrence
      sameParameter candidate =
        grammarV1ResolvedBinderKey candidate == grammarV1ResolvedBinderKey binder
  in if grammarV1ResolvedBinderKind binder == GrammarV1ComponentParameterBinder
      && any sameParameter parameters
    then Right ()
    else Left (GrammarV1RequestReplyOperandNotParameter role binder)

bindIdentifier
  :: Text
  -> Located GrammarV1Pattern
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1RequestReplyOutputError
      (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindIdentifier role patternSource scope =
  case locatedValue patternSource of
    GrammarV1IdentifierPattern _ -> do
      (binders, nextScope) <- mapLeft
        GrammarV1RequestReplyBinderError
        (grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope)
      case binders of
        [binder] -> Right (binder, nextScope)
        _ -> Left (GrammarV1RequestReplyPatternShape role)
    _ -> Left (GrammarV1RequestReplyPatternShape role)

bindTuple2
  :: Text
  -> Located GrammarV1Pattern
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1RequestReplyOutputError
      (GrammarV1ResolvedBinder, GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindTuple2 role patternSource scope =
  case locatedValue patternSource of
    GrammarV1TuplePattern
      [ Located _ (GrammarV1IdentifierPattern _)
      , Located _ (GrammarV1IdentifierPattern _)
      ] -> do
        (binders, nextScope) <- mapLeft
          GrammarV1RequestReplyBinderError
          (grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope)
        case binders of
          [first, second] -> Right (first, second, nextScope)
          _ -> Left (GrammarV1RequestReplyPatternShape role)
    _ -> Left (GrammarV1RequestReplyPatternShape role)

requireSameBinder
  :: Text
  -> GrammarV1ResolvedBinder
  -> GrammarV1ResolvedBinder
  -> Either GrammarV1RequestReplyOutputError ()
requireSameBinder role expected actual
  | grammarV1ResolvedBinderKey expected == grammarV1ResolvedBinderKey actual = Right ()
  | otherwise = Left (GrammarV1RequestReplyEndpointMismatch role expected actual)

requireType
  :: GrammarV1Type
  -> GrammarV1Type
  -> Either GrammarV1RequestReplyOutputError ()
requireType expected actual
  | expected == actual = Right ()
  | otherwise = Left (GrammarV1RequestReplyReceiveTypeMismatch expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
