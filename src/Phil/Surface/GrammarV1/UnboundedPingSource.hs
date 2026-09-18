{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.UnboundedPingSource
  ( GrammarV1CheckedUnboundedPingSource (..)
  , GrammarV1UnboundedPingSourceError (..)
  , grammarV1CheckedUnboundedPingSource
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopSlot (..)
  , GrammarV1CheckedLoopState (..)
  , grammarV1CheckedLoopExpressionInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1BranchValue (..)
  , GrammarV1ComponentDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1Pattern (..)
  , GrammarV1Statement (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  , grammarV1QualifiedNameParts
  , pattern GrammarV1StringExpression
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1CheckedUnboundedPingSource = GrammarV1CheckedUnboundedPingSource
  { unboundedPingClientEndpointParameter :: GrammarV1ResolvedBinder
  , unboundedPingServerEndpointParameter :: GrammarV1ResolvedBinder
  , unboundedPingClientEndpointState :: GrammarV1ResolvedBinder
  , unboundedPingServerEndpointState :: GrammarV1ResolvedBinder
  , unboundedPingSourceRequestValue :: ScalarLiteral
  , unboundedPingSourceReplyText :: Text
  }
  deriving (Eq, Show)

data GrammarV1UnboundedPingSourceError
  = GrammarV1UnboundedPingClientShape Text
  | GrammarV1UnboundedPingServerShape Text
  | GrammarV1UnboundedPingRequestOutOfRange Integer
  | GrammarV1UnboundedPingReferenceMismatch Text
  deriving (Eq, Show)

grammarV1CheckedUnboundedPingSource
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1UnboundedPingSourceError
        GrammarV1CheckedUnboundedPingSource)
grammarV1CheckedUnboundedPingSource clientKey client serverKey server = do
  (clientParameter, clientLoop) <- checkedLoop clientKey client
  (serverParameter, serverLoop) <- checkedLoop serverKey server
  pure $ do
    (clientState, request) <- checkedClientRound clientLoop
    (serverState, reply) <- checkedServerRound serverLoop
    Right GrammarV1CheckedUnboundedPingSource
      { unboundedPingClientEndpointParameter = clientParameter
      , unboundedPingServerEndpointParameter = serverParameter
      , unboundedPingClientEndpointState = clientState
      , unboundedPingServerEndpointState = serverState
      , unboundedPingSourceRequestValue = request
      , unboundedPingSourceReplyText = reply
      }

checkedLoop
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe (GrammarV1ResolvedBinder, GrammarV1CheckedLoopState)
checkedLoop declarationKey component = do
  (maybeParameters, parameterScope) <- either (const Nothing) Just
    (grammarV1ComponentParameterScope declarationKey component)
  endpointParameter <- case maybeParameters of
    Just [parameter]
      | grammarV1ResolvedBinderDisplayName parameter == "endpoint" -> Just parameter
    _ -> Nothing
  loopSource <- case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block [Located _ (GrammarV1ExpressionStatement expression)] -> Just expression
    _ -> Nothing
  checked <- grammarV1CheckedLoopExpressionInScope parameterScope loopSource
  loopState <- either (const Nothing) (Just . fst) checked
  Just (endpointParameter, loopState)

checkedClientRound
  :: GrammarV1CheckedLoopState
  -> Either
      GrammarV1UnboundedPingSourceError
      (GrammarV1ResolvedBinder, ScalarLiteral)
checkedClientRound checked = do
  currentEndpoint <- endpointState "client" (grammarV1CheckedLoopSlots checked)
  case grammarV1CheckedLoopBodySteps checked of
    [ GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement selectedPattern selectedSource))
        selectedRefs
        [selected]
      , GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement awaitingPattern sendSource))
        sendRefs
        [awaiting]
      , GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement receivePattern receiveSource))
        receiveRefs
        [nextEndpoint, reply]
      , GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement writePattern writeSource))
        writeRefs
        [_writeDecision]
      , GrammarV1CheckedLoopContinueStep _ _ continueRefs
      ] -> do
        requireIdentifier clientShape "selected" selectedPattern
        requireIdentifier clientShape "awaiting" awaitingPattern
        requireTuple2 clientShape "receive result" receivePattern
        requireIdentifier clientShape "writeDecision" writePattern
        case locatedValue selectedSource of
          GrammarV1SelectExpression branch endpoint Nothing
            | branchName branch == "Ping" -> do
                requireReferences "select endpoint" [currentEndpoint] selectedRefs
                requireSimpleName clientShape "select endpoint syntax" "currentEndpoint" endpoint
            | otherwise -> clientShape "select branch is not Ping"
          _ -> clientShape "expected select Ping on currentEndpoint"
        request <- case locatedValue sendSource of
          GrammarV1SendExpression value endpoint -> do
            requireReferences "send endpoint" [selected] sendRefs
            requireSimpleName clientShape "send endpoint syntax" "selected" endpoint
            parseRequestByte value
          _ -> clientShape "expected literal request send"
        case locatedValue receiveSource of
          GrammarV1ReceiveExpression receiveType endpoint -> do
            requireStringType receiveType
            requireReferences "receive endpoint" [awaiting] receiveRefs
            requireSimpleName clientShape "receive endpoint syntax" "awaiting" endpoint
          _ -> clientShape "expected String receive"
        case locatedValue writeSource of
          GrammarV1NameExpression reference [argument]
            | referenceName reference == ["console_write"] -> do
                requireReferences "console_write reply" [reply] writeRefs
                requireSimpleName clientShape "console_write argument" "reply" argument
            | otherwise -> clientShape "expected console_write(reply)"
          _ -> clientShape "expected console_write(reply)"
        requireReferences "client continue" [nextEndpoint] continueRefs
        Right (currentEndpoint, request)
    _ -> clientShape "expected select/send/receive/output/continue loop body"

checkedServerRound
  :: GrammarV1CheckedLoopState
  -> Either
      GrammarV1UnboundedPingSourceError
      (GrammarV1ResolvedBinder, Text)
checkedServerRound checked = do
  currentEndpoint <- endpointState "server" (grammarV1CheckedLoopSlots checked)
  case grammarV1CheckedLoopBodySteps checked of
    [ GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement receivePattern receiveSource))
        receiveRefs
        [replyEndpoint, _request]
      , GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement sendPattern sendSource))
        sendRefs
        [nextEndpoint]
      , GrammarV1CheckedLoopContinueStep _ _ continueRefs
      ] -> do
        requireTuple2 serverShape "server receive result" receivePattern
        requireIdentifier serverShape "nextEndpoint" sendPattern
        case locatedValue receiveSource of
          GrammarV1ReceiveExpression receiveType endpoint -> do
            requireU8Type receiveType
            requireReferences "server receive endpoint" [currentEndpoint] receiveRefs
            requireSimpleName serverShape "server receive endpoint syntax" "currentEndpoint" endpoint
          _ -> serverShape "expected U8 receive"
        reply <- case locatedValue sendSource of
          GrammarV1SendExpression value endpoint -> do
            replyText <- case locatedValue value of
              GrammarV1StringExpression text -> Right text
              _ -> serverShape "reply must be a String literal"
            requireReferences "server send endpoint" [replyEndpoint] sendRefs
            requireSimpleName serverShape "server send endpoint syntax" "replyEndpoint" endpoint
            Right replyText
          _ -> serverShape "expected literal reply send"
        requireReferences "server continue" [nextEndpoint] continueRefs
        Right (currentEndpoint, reply)
    _ -> serverShape "expected receive/send/continue loop body"

endpointState
  :: Text
  -> [GrammarV1CheckedLoopSlot]
  -> Either GrammarV1UnboundedPingSourceError GrammarV1ResolvedBinder
endpointState side slots = case slots of
  [slot]
    | grammarV1ResolvedBinderDisplayName (grammarV1CheckedLoopSlotBinder slot)
        == "currentEndpoint" ->
        Right (grammarV1CheckedLoopSlotBinder slot)
  _
    | side == "client" -> clientShape "expected currentEndpoint loop state"
    | otherwise -> serverShape "expected currentEndpoint loop state"

parseRequestByte
  :: Located GrammarV1Expression
  -> Either GrammarV1UnboundedPingSourceError ScalarLiteral
parseRequestByte (Located _ expression) = case expression of
  GrammarV1IntegerExpression raw ->
    case reads (Text.unpack raw) of
      [(value, "")]
        | value >= 0 && value <= 255 -> Right (ScalarUIntLiteral 8 value)
        | otherwise -> Left (GrammarV1UnboundedPingRequestOutOfRange value)
      _ -> clientShape "request literal is not an integer"
  _ -> clientShape "request must be an integer literal"

requireStringType
  :: Located GrammarV1Type
  -> Either GrammarV1UnboundedPingSourceError ()
requireStringType (Located _ (GrammarV1UnsignedType "String")) = Right ()
requireStringType _ = clientShape "reply receive type must be String"

requireU8Type
  :: Located GrammarV1Type
  -> Either GrammarV1UnboundedPingSourceError ()
requireU8Type (Located _ (GrammarV1UnsignedType "U8")) = Right ()
requireU8Type _ = serverShape "request receive type must be U8"

requireIdentifier
  :: (Text -> Either GrammarV1UnboundedPingSourceError ())
  -> Text
  -> Located GrammarV1Pattern
  -> Either GrammarV1UnboundedPingSourceError ()
requireIdentifier _shape expected (Located _ (GrammarV1IdentifierPattern name))
  | locatedValue name == expected = Right ()
requireIdentifier shape expected _ = shape ("unexpected binder for " <> expected)

requireTuple2
  :: (Text -> Either GrammarV1UnboundedPingSourceError ())
  -> Text
  -> Located GrammarV1Pattern
  -> Either GrammarV1UnboundedPingSourceError ()
requireTuple2 _ _ (Located _ (GrammarV1TuplePattern [_, _])) = Right ()
requireTuple2 shape role _ = shape ("unexpected tuple pattern for " <> role)

requireReferences
  :: Text
  -> [GrammarV1ResolvedBinder]
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1UnboundedPingSourceError ()
requireReferences role expected references
  | map grammarV1ResolvedBinderKey expected
      == map
        (grammarV1ResolvedBinderKey . grammarV1CheckedLexicalReferenceBinder)
        references = Right ()
  | otherwise = Left (GrammarV1UnboundedPingReferenceMismatch role)

requireSimpleName
  :: (Text -> Either GrammarV1UnboundedPingSourceError ())
  -> Text
  -> Text
  -> Located GrammarV1Expression
  -> Either GrammarV1UnboundedPingSourceError ()
requireSimpleName shape role expected (Located _ expression) =
  case expression of
    GrammarV1NameExpression reference []
      | referenceName reference == [expected] -> Right ()
    GrammarV1ParenthesizedExpression inner -> requireSimpleName shape role expected inner
    _ -> shape ("unexpected local syntax for " <> role)

branchName :: Located GrammarV1BranchValue -> Text
branchName (Located _ branch) =
  case grammarV1QualifiedNameParts
      (locatedValue (grammarV1BranchValueName branch)) of
    [name] -> name
    _ -> ""

referenceName :: GrammarV1StaticReference -> [Text]
referenceName = grammarV1QualifiedNameParts . grammarV1StaticReferenceName

clientShape :: Text -> Either GrammarV1UnboundedPingSourceError a
clientShape = Left . GrammarV1UnboundedPingClientShape

serverShape :: Text -> Either GrammarV1UnboundedPingSourceError a
serverShape = Left . GrammarV1UnboundedPingServerShape
