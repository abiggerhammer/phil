-- FSEM-02 (non-normative): an exact parsed-source send/receive pair may
-- advance one activation-owned restricted payload through the existing Core
-- atomic rendezvous. Neither the nominal roles nor the payload occurrence
-- is derived from display spelling; all are explicit external inputs.
module Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
  ( GrammarV1RestrictedSourceError (..)
  , GrammarV1RestrictedSourceTransition (..)
  , grammarV1CheckRestrictedSourceRendezvous
  ) where

import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessActivation (ActivationOccurrenceKey)
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , RestrictedMessageTransfer (..)
  , checkRestrictedProcessRendezvous
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family (BinaryProtocolInstance (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Ty)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1CheckedComponentReceiveClose (..)
  , GrammarV1ComponentReceiveCloseError
  , grammarV1CheckedComponentReceiveClose
  )
import Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1CheckedComponentSendClose (..)
  , GrammarV1ComponentSendCloseError
  , grammarV1CheckedComponentSendClose
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1RestrictedSourceError
  = RestrictedSourceSendShapeUnsupported
  | RestrictedSourceSendError GrammarV1ComponentSendCloseError
  | RestrictedSourceReceiveShapeUnsupported
  | RestrictedSourceReceiveError GrammarV1ComponentReceiveCloseError
  | RestrictedSourceParameterScopeError GrammarV1BinderScopeError
  | RestrictedSourceParameterShapeMismatch
  | RestrictedSourcePayloadParameterMissing
  | RestrictedSourcePayloadTypeUnsupported
  | RestrictedSourcePayloadTypeError FocusingError
  | RestrictedSourceReceiveTypeUnsupported
  | RestrictedSourceReceiveTypeError FocusingError
  | RestrictedSourcePayloadModeNotRestricted Mode
  | RestrictedSourceReceiveModeMismatch Mode Mode
  | RestrictedSourceMessageTypeMismatch Ty Ty
  | RestrictedSourceCoreError ProcessRendezvousError
  deriving (Eq, Show)

data GrammarV1RestrictedSourceTransition = GrammarV1RestrictedSourceTransition
  { restrictedSourceSend :: GrammarV1CheckedComponentSendClose
  , restrictedSourceReceive :: GrammarV1CheckedComponentReceiveClose
  , restrictedSourceTransfer :: RestrictedMessageTransfer
  , restrictedSourceRequest :: ProcessRendezvousRequest
  , restrictedSourceNext :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | Preconditions are deliberately explicit:
--   * both exact two-statement source component bodies are independently
--     parsed and checked for binder identity and terminal-close shape;
--   * the sender's source parameter type/mode and the receiver's written
--     type/mode must be checked through the production type checker;
--   * the caller supplies the binary protocol's independently checked
--     instance, exact role/process/network identities, an activation-derived
--     owner occurrence, and the live communication state.
--
-- Only the production checkRestrictedProcessRendezvous decides whether the
-- matched dual heads, exact owner occurrence, payload resource, and receiver
-- insertion can all progress atomically. On any error no successor is returned.
-- Source close statements are checked for shape but NOT executed here.
grammarV1CheckRestrictedSourceRendezvous
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> ActivationOccurrenceKey
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> Either GrammarV1RestrictedSourceError GrammarV1RestrictedSourceTransition
grammarV1CheckRestrictedSourceRendezvous
    staticContext senderRoot senderSource receiverRoot receiverSource
    instanceValue senderRole receiverRole senderProcess receiverProcess
    occurrence network state = do
  sendPlan <- case grammarV1CheckedComponentSendClose senderRoot senderSource of
    Nothing -> Left RestrictedSourceSendShapeUnsupported
    Just result -> mapLeft RestrictedSourceSendError result
  receivePlan <- case grammarV1CheckedComponentReceiveClose receiverRoot receiverSource of
    Nothing -> Left RestrictedSourceReceiveShapeUnsupported
    Just result -> mapLeft RestrictedSourceReceiveError result
  sourceType <- senderPayloadType senderRoot senderSource
    (checkedComponentSendPayload sendPlan)
  senderMode <- case grammarV1CheckedTypeMode
      staticContext emptySurfaceState sourceType of
    Nothing -> Left RestrictedSourcePayloadTypeUnsupported
    Just result -> mapLeft RestrictedSourcePayloadTypeError result
  receiverMode <- case grammarV1CheckedTypeMode
      staticContext emptySurfaceState
      (checkedComponentReceiveWrittenType receivePlan) of
    Nothing -> Left RestrictedSourceReceiveTypeUnsupported
    Just result -> mapLeft RestrictedSourceReceiveTypeError result
  let (senderChecked, _) = senderMode
      (receiverChecked, _) = receiverMode
      payloadMode = checkedBindingMode senderChecked
      payloadType = checkedBindingType senderChecked
  case payloadMode of
    Linear -> Right ()
    Affine -> Right ()
    other -> Left (RestrictedSourcePayloadModeNotRestricted other)
  if checkedBindingType receiverChecked == payloadType
    then Right ()
    else Left (RestrictedSourceMessageTypeMismatch
      payloadType (checkedBindingType receiverChecked))
  if checkedBindingMode receiverChecked == payloadMode
    then Right ()
    else Left (RestrictedSourceReceiveModeMismatch
      payloadMode (checkedBindingMode receiverChecked))
  let revision = binaryProtocolInstanceRevision instanceValue
      senderSide = ProcessRendezvousSide
        { rendezvousProcess = senderProcess
        , rendezvousEndpoint = grammarV1ResolvedBinderCoreName
            (checkedComponentSendEndpoint sendPlan)
        , rendezvousSuccessor = grammarV1ResolvedBinderCoreName
            (checkedComponentSendSuccessor sendPlan)
        , rendezvousInstance = revision
        , rendezvousRole = senderRole
        }
      receiverSide = ProcessRendezvousSide
        { rendezvousProcess = receiverProcess
        , rendezvousEndpoint = grammarV1ResolvedBinderCoreName
            (checkedComponentReceiveEndpoint receivePlan)
        , rendezvousSuccessor = grammarV1ResolvedBinderCoreName
            (checkedComponentReceiveSuccessor receivePlan)
        , rendezvousInstance = revision
        , rendezvousRole = receiverRole
        }
      transfer = RestrictedMessageTransfer
        { restrictedMessageOccurrence = occurrence
        , restrictedMessageSenderName = grammarV1ResolvedBinderCoreName
            (checkedComponentSendPayload sendPlan)
        , restrictedMessageReceiverName = grammarV1ResolvedBinderCoreName
            (checkedComponentReceivePayload receivePlan)
        , restrictedMessageMode = payloadMode
        , restrictedMessageType = payloadType
        }
      request = SendReceiveRendezvous senderSide receiverSide
  next <- mapLeft RestrictedSourceCoreError $
    checkRestrictedProcessRendezvous instanceValue network state request transfer
  pure GrammarV1RestrictedSourceTransition
    { restrictedSourceSend = sendPlan
    , restrictedSourceReceive = receivePlan
    , restrictedSourceTransfer = transfer
    , restrictedSourceRequest = request
    , restrictedSourceNext = next
    }

senderPayloadType
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> GrammarV1ResolvedBinder
  -> Either GrammarV1RestrictedSourceError GrammarV1Type
senderPayloadType root source payload = do
  (maybeBinders, _) <- mapLeft RestrictedSourceParameterScopeError
    (grammarV1ComponentParameterScope root source)
  let binders = maybe [] id maybeBinders
      parameters = maybe [] id (grammarV1ComponentTermParams source)
      matches =
        [ locatedValue (grammarV1TermParamType parameter)
        | (binder, Located _ parameter) <- zip binders parameters
        , grammarV1ResolvedBinderKey binder ==
            grammarV1ResolvedBinderKey payload
        ]
  if length binders /= length parameters
    then Left RestrictedSourceParameterShapeMismatch
    else case matches of
      [sourceType] -> Right sourceType
      _ -> Left RestrictedSourcePayloadParameterMissing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
