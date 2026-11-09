-- Non-normative FSEM-02: execute the two source-checked terminal closes
-- *after* a successfully checked restricted send/receive rendezvous.
-- Protocol/role/process/activation authority and terminal outcomes remain
-- explicit inputs; this module does not admit a complete source architecture.
module Phil.Surface.GrammarV1.ComponentRestrictedSourceClose
  ( GrammarV1RestrictedSourceCloseError (..)
  , GrammarV1RestrictedSourceCloseTransition (..)
  , grammarV1CheckRestrictedSourceClose
  ) where

import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError
  , closeProcessEndpointState
  )
import Phil.Core.ProcessRendezvous (ProcessCommunicationState)
import Phil.Core.Protocol (ProtocolInstanceRevision, ProtocolRoleKey)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name, Outcome)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1ComponentReceiveCloseError
  , GrammarV1CheckedComponentReceiveClose (..)
  , grammarV1CheckedComponentReceiveClose
  )
import Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
  ( GrammarV1RestrictedSourceTransition (..)
  )
import Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1ComponentSendCloseError
  , GrammarV1CheckedComponentSendClose (..)
  , grammarV1CheckedComponentSendClose
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1RestrictedSourceCloseError
  = RestrictedSourceCloseSenderUnsupported
  | RestrictedSourceCloseSenderError GrammarV1ComponentSendCloseError
  | RestrictedSourceCloseReceiverUnsupported
  | RestrictedSourceCloseReceiverError GrammarV1ComponentReceiveCloseError
  | RestrictedSourceCloseSenderPlanChanged
  | RestrictedSourceCloseReceiverPlanChanged
  | RestrictedSourceCloseSenderCoreError ProcessEndpointClosureError
  | RestrictedSourceCloseReceiverCoreError ProcessEndpointClosureError
  deriving (Eq, Show)

data GrammarV1RestrictedSourceCloseTransition =
  GrammarV1RestrictedSourceCloseTransition
    { restrictedSourceClosedSender :: Name
    , restrictedSourceClosedReceiver :: Name
    , restrictedSourceCloseNext :: ProcessCommunicationState
    }
  deriving (Eq, Show)

-- | Judgment:
--   (checkedSource, livePostRendezvous, network, explicit roles/outcomes)
--     --close sender; close receiver--> postCloseState
--
-- Only the exact parsed send/close and receive/close bodies are in scope.
-- Rechecking their declaration-rooted binders prevents a cached rendezvous
-- plan from silently authorizing a different source close expression.
-- The Core close checker validates each live End head, endpoint resource,
-- role/instance revision and unique activation-owned occurrence. Its result
-- consumes the endpoint's predecessor resource and retires exactly that
-- occurrence. The intermediate sender-close state never escapes on receiver
-- failure, so this compound pure check returns either both closes or no state.
-- Remaining payload resources and process/root terminal obligations are NOT
-- discharged by this endpoint-close operation.
grammarV1CheckRestrictedSourceClose
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> ProcessNetwork
  -> GrammarV1RestrictedSourceTransition
  -> ProcessKey
  -> ProcessKey
  -> ProtocolInstanceRevision
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> Outcome
  -> Outcome
  -> Either
       GrammarV1RestrictedSourceCloseError
       GrammarV1RestrictedSourceCloseTransition
grammarV1CheckRestrictedSourceClose
    senderRoot senderSource receiverRoot receiverSource network rendezvous
    senderProcess receiverProcess revision senderRole receiverRole
    senderOutcome receiverOutcome = do
  sender <- case grammarV1CheckedComponentSendClose senderRoot senderSource of
    Nothing -> Left RestrictedSourceCloseSenderUnsupported
    Just result -> mapLeft RestrictedSourceCloseSenderError result
  receiver <- case grammarV1CheckedComponentReceiveClose receiverRoot receiverSource of
    Nothing -> Left RestrictedSourceCloseReceiverUnsupported
    Just result -> mapLeft RestrictedSourceCloseReceiverError result
  if sender == restrictedSourceSend rendezvous
    then Right ()
    else Left RestrictedSourceCloseSenderPlanChanged
  if receiver == restrictedSourceReceive rendezvous
    then Right ()
    else Left RestrictedSourceCloseReceiverPlanChanged
  let senderEndpoint = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor sender)
      receiverEndpoint = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor receiver)
  afterSender <- mapLeft RestrictedSourceCloseSenderCoreError $
    closeProcessEndpointState network (restrictedSourceNext rendezvous)
      senderProcess senderEndpoint revision senderRole senderOutcome
  afterReceiver <- mapLeft RestrictedSourceCloseReceiverCoreError $
    closeProcessEndpointState network afterSender
      receiverProcess receiverEndpoint revision receiverRole receiverOutcome
  pure GrammarV1RestrictedSourceCloseTransition
    { restrictedSourceClosedSender = senderEndpoint
    , restrictedSourceClosedReceiver = receiverEndpoint
    , restrictedSourceCloseNext = afterReceiver
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
