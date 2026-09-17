{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.GrammarV1.BoundedPingSourceValues
  ( GrammarV1BoundedPingSourceValues (..)
  , GrammarV1BoundedPingSourceValuesError (..)
  , grammarV1CheckedBoundedPingSourceValues
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1ResolvedBinder (..)
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
  ( GrammarV1BinaryOperator (..)
  , GrammarV1Block (..)
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

-- | Source-derived values for one positive bounded-Ping round.  These are the
-- concrete values that #1149 previously accepted as runtime fixture arguments.
data GrammarV1BoundedPingSourceValues = GrammarV1BoundedPingSourceValues
  { boundedPingSourceRequestValue :: ScalarLiteral
  , boundedPingSourceReplyText :: Text
  }
  deriving (Eq, Show)

data GrammarV1BoundedPingSourceValuesError
  = GrammarV1BoundedPingSourceValuesClientShape Text
  | GrammarV1BoundedPingSourceValuesServerShape Text
  | GrammarV1BoundedPingSourceValuesRequestOutOfRange Integer
  | GrammarV1BoundedPingSourceValuesReferenceMismatch Text
  deriving (Eq, Show)

-- | Check explicit positive-round loop bodies and extract the exact request byte
-- and reply text.  The client body must spell select/send/receive/output/
-- decrement/continue in one lexical chain.  The server round template must
-- receive, send a literal String reply, and carry the successor endpoint back.
grammarV1CheckedBoundedPingSourceValues
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1BoundedPingSourceValuesError
        GrammarV1BoundedPingSourceValues)
grammarV1CheckedBoundedPingSourceValues clientKey client serverKey server = do
  clientChecked <- checkedLoop clientKey client
  serverChecked <- checkedLoop serverKey server
  pure $ do
    request <- checkedClientRound clientChecked
    reply <- checkedServerRound serverChecked
    Right GrammarV1BoundedPingSourceValues
      { boundedPingSourceRequestValue = request
      , boundedPingSourceReplyText = reply
      }

checkedLoop
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> Maybe GrammarV1CheckedLoopState
checkedLoop declarationKey component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block [Located _ (GrammarV1ExpressionStatement loopSource)] -> do
      (maybeParameters, parameterScope) <- either (const Nothing) Just
        (grammarV1ComponentParameterScope declarationKey component)
      _ <- Just (maybe [] id maybeParameters)
      checked <- grammarV1CheckedLoopExpressionInScope parameterScope loopSource
      either (const Nothing) (Just . fst) checked
    _ -> Nothing

checkedClientRound
  :: GrammarV1CheckedLoopState
  -> Either GrammarV1BoundedPingSourceValuesError ScalarLiteral
checkedClientRound checked = do
  (currentEndpoint, remaining) <- case grammarV1CheckedLoopSlots checked of
    [endpointSlot, countSlot]
      | binderName (grammarV1CheckedLoopSlotBinder endpointSlot) == "currentEndpoint"
      , binderName (grammarV1CheckedLoopSlotBinder countSlot) == "remaining" ->
          Right
            ( grammarV1CheckedLoopSlotBinder endpointSlot
            , grammarV1CheckedLoopSlotBinder countSlot
            )
    _ -> clientShape "expected currentEndpoint/remaining loop state"
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
      , GrammarV1CheckedLoopBodyLetStep
        (Located _ (GrammarV1LetStatement nextCountPattern decrementSource))
        decrementRefs
        [nextRemaining]
      , GrammarV1CheckedLoopContinueStep _ _ continueRefs
      ] -> do
        requireIdentifier "selected" selectedPattern
        requireIdentifier "awaiting" awaitingPattern
        requireTuple2 "receive result" receivePattern
        requireIdentifier "writeDecision" writePattern
        requireIdentifier "nextRemaining" nextCountPattern
        request <- case locatedValue selectedSource of
          GrammarV1SelectExpression branch endpoint Nothing
            | branchName branch == "Ping" -> do
                requireSingleReference "select endpoint" currentEndpoint selectedRefs
                requireSimpleName "select endpoint syntax" "currentEndpoint" endpoint
                Right ()
            | otherwise -> clientShape "select branch is not Ping"
          _ -> clientShape "expected select Ping on currentEndpoint"
        _ <- Right request
        requestValue <- case locatedValue sendSource of
          GrammarV1SendExpression value endpoint -> do
            requireSingleReference "send endpoint" selected sendRefs
            requireSimpleName "send endpoint syntax" "selected" endpoint
            parseRequestByte value
          _ -> clientShape "expected literal request send"
        case locatedValue receiveSource of
          GrammarV1ReceiveExpression receiveType endpoint -> do
            requireStringType receiveType
            requireSingleReference "receive endpoint" awaiting receiveRefs
            requireSimpleName "receive endpoint syntax" "awaiting" endpoint
          _ -> clientShape "expected String receive"
        case locatedValue writeSource of
          GrammarV1NameExpression reference [argument]
            | referenceName reference == ["console_write"] -> do
                requireSingleReference "console_write reply" reply writeRefs
                requireSimpleName "console_write argument" "reply" argument
            | otherwise -> clientShape "expected console_write(reply)"
          _ -> clientShape "expected console_write(reply)"
        case locatedValue decrementSource of
          GrammarV1BinaryExpression left (Located _ GrammarV1Subtract) right -> do
            requireSingleReference "decrement source" remaining decrementRefs
            requireSimpleName "decrement lhs" "remaining" left
            case locatedValue right of
              GrammarV1IntegerExpression "1" -> Right ()
              _ -> clientShape "decrement must subtract literal 1"
          _ -> clientShape "expected remaining - 1"
        requireReferences "continue backedge" [nextEndpoint, nextRemaining] continueRefs
        Right requestValue
    _ -> clientShape "expected select/send/receive/output/decrement/continue body"

checkedServerRound
  :: GrammarV1CheckedLoopState
  -> Either GrammarV1BoundedPingSourceValuesError Text
checkedServerRound checked = do
  currentEndpoint <- case grammarV1CheckedLoopSlots checked of
    [endpointSlot]
      | binderName (grammarV1CheckedLoopSlotBinder endpointSlot) == "currentEndpoint" ->
          Right (grammarV1CheckedLoopSlotBinder endpointSlot)
    _ -> serverShape "expected currentEndpoint loop state"
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
        requireTuple2Server receivePattern
        requireIdentifierServer "nextEndpoint" sendPattern
        case locatedValue receiveSource of
          GrammarV1ReceiveExpression receiveType endpoint -> do
            requireU8Type receiveType
            requireSingleReferenceServer "server receive endpoint" currentEndpoint receiveRefs
            requireSimpleNameServer "server receive endpoint syntax" "currentEndpoint" endpoint
          _ -> serverShape "expected U8 receive"
        reply <- case locatedValue sendSource of
          GrammarV1SendExpression value endpoint -> do
            requireSingleReferenceServer "server send endpoint" replyEndpoint sendRefs
            requireSimpleNameServer "server send endpoint syntax" "replyEndpoint" endpoint
            case locatedValue value of
              GrammarV1StringExpression text -> Right text
              _ -> serverShape "reply must be a String literal"
          _ -> serverShape "expected literal reply send"
        requireReferencesServer "server continue" [nextEndpoint] continueRefs
        Right reply
    _ -> serverShape "expected receive/send/continue round body"

parseRequestByte
  :: Located GrammarV1Expression
  -> Either GrammarV1BoundedPingSourceValuesError ScalarLiteral
parseRequestByte (Located _ expression) = case expression of
  GrammarV1IntegerExpression raw ->
    case reads (Text.unpack raw) of
      [(value, "")]
        | value >= 0 && value <= 255 -> Right (ScalarUIntLiteral 8 value)
        | otherwise -> Left (GrammarV1BoundedPingSourceValuesRequestOutOfRange value)
      _ -> clientShape "request literal is not an integer"
  _ -> clientShape "request must be an integer literal"

requireStringType :: Located GrammarV1Type -> Either GrammarV1BoundedPingSourceValuesError ()
requireStringType (Located _ (GrammarV1UnsignedType "String")) = Right ()
requireStringType _ = clientShape "reply receive type must be String"

requireU8Type :: Located GrammarV1Type -> Either GrammarV1BoundedPingSourceValuesError ()
requireU8Type (Located _ (GrammarV1UnsignedType "U8")) = Right ()
requireU8Type _ = serverShape "request receive type must be U8"

requireIdentifier
  :: Text
  -> Located GrammarV1Pattern
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireIdentifier role (Located _ (GrammarV1IdentifierPattern name))
  | locatedValue name == role = Right ()
requireIdentifier role _ = clientShape ("unexpected binder for " <> role)

requireIdentifierServer
  :: Text
  -> Located GrammarV1Pattern
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireIdentifierServer role (Located _ (GrammarV1IdentifierPattern name))
  | locatedValue name == role = Right ()
requireIdentifierServer role _ = serverShape ("unexpected binder for " <> role)

requireTuple2
  :: Text
  -> Located GrammarV1Pattern
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireTuple2 _ (Located _ (GrammarV1TuplePattern [_, _])) = Right ()
requireTuple2 role _ = clientShape ("unexpected tuple pattern for " <> role)

requireTuple2Server
  :: Located GrammarV1Pattern
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireTuple2Server (Located _ (GrammarV1TuplePattern [_, _])) = Right ()
requireTuple2Server _ = serverShape "unexpected server receive tuple pattern"

requireSingleReference
  :: Text
  -> GrammarV1ResolvedBinder
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireSingleReference role expected references = requireReferences role [expected] references

requireSingleReferenceServer
  :: Text
  -> GrammarV1ResolvedBinder
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireSingleReferenceServer role expected references = requireReferencesServer role [expected] references

requireReferences
  :: Text
  -> [GrammarV1ResolvedBinder]
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireReferences role expected references
  | map binderKey expected == map (binderKey . grammarV1CheckedLexicalReferenceBinder) references = Right ()
  | otherwise = Left (GrammarV1BoundedPingSourceValuesReferenceMismatch role)

requireReferencesServer
  :: Text
  -> [GrammarV1ResolvedBinder]
  -> [GrammarV1CheckedLexicalReference]
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireReferencesServer role expected references
  | map binderKey expected == map (binderKey . grammarV1CheckedLexicalReferenceBinder) references = Right ()
  | otherwise = Left (GrammarV1BoundedPingSourceValuesReferenceMismatch role)

requireSimpleName
  :: Text
  -> Text
  -> Located GrammarV1Expression
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireSimpleName role expected (Located _ expression) =
  case expression of
    GrammarV1NameExpression reference []
      | referenceName reference == [expected] -> Right ()
    GrammarV1ParenthesizedExpression inner -> requireSimpleName role expected inner
    _ -> clientShape ("unexpected local syntax for " <> role)

requireSimpleNameServer
  :: Text
  -> Text
  -> Located GrammarV1Expression
  -> Either GrammarV1BoundedPingSourceValuesError ()
requireSimpleNameServer role expected (Located _ expression) =
  case expression of
    GrammarV1NameExpression reference []
      | referenceName reference == [expected] -> Right ()
    GrammarV1ParenthesizedExpression inner -> requireSimpleNameServer role expected inner
    _ -> serverShape ("unexpected local syntax for " <> role)

branchName :: Located GrammarV1BranchValue -> Text
branchName (Located _ branch) =
  case grammarV1QualifiedNameParts (locatedValue (grammarV1BranchValueName branch)) of
    [name] -> name
    _ -> ""

referenceName :: GrammarV1StaticReference -> [Text]
referenceName = grammarV1QualifiedNameParts . grammarV1StaticReferenceName

binderName :: GrammarV1ResolvedBinder -> Text
binderName = grammarV1ResolvedBinderDisplayName

binderKey :: GrammarV1ResolvedBinder -> GrammarV1BinderKey
binderKey = grammarV1ResolvedBinderKey

clientShape :: Text -> Either GrammarV1BoundedPingSourceValuesError a
clientShape = Left . GrammarV1BoundedPingSourceValuesClientShape

serverShape :: Text -> Either GrammarV1BoundedPingSourceValuesError a
serverShape = Left . GrammarV1BoundedPingSourceValuesServerShape
