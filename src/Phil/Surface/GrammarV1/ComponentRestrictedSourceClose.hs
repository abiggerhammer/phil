-- Non-normative FSEM-02: execute the two source-checked terminal closes
-- *after* a successfully checked restricted send/receive rendezvous.
-- Protocol/role/process/activation authority and terminal outcomes remain
-- explicit inputs; this module does not admit a complete source architecture.
module Phil.Surface.GrammarV1.ComponentRestrictedSourceClose
  ( GrammarV1RestrictedSourceCloseError (..)
  , GrammarV1RestrictedSourceCloseTransition (..)
  , grammarV1CheckRestrictedSourceClose
  , GrammarV1RestrictedSourceCloseDiamondError (..)
  , GrammarV1RestrictedSourceCloseDiamondTransition (..)
  , grammarV1CheckRestrictedSourceCloseDiamond
  , GrammarV1RestrictedSourceSuccessorTraceError (..)
  , GrammarV1RestrictedSourceSuccessorTrace (..)
  , grammarV1CheckRestrictedSourceSuccessorTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessActivation (ActivationOccurrenceKey)
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError
  , closeProcessEndpointState
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , RestrictedMessageTransfer (..)
  )
import Phil.Core.Protocol (ProtocolInstanceRevision, ProtocolRoleKey)
import Phil.Core.Protocol.Family (BinaryProtocolInstance (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Name, Outcome)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1ComponentReceiveCloseError
  , GrammarV1CheckedComponentReceiveClose (..)
  , grammarV1CheckedComponentReceiveClose
  )
import Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
  ( GrammarV1RestrictedSourceError
  , GrammarV1RestrictedSourceTransition (..)
  , grammarV1CheckRestrictedSourceRendezvous
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
  | RestrictedSourceCloseRequestMismatch
      ProcessRendezvousRequest ProcessRendezvousRequest
  | RestrictedSourceCloseTransferBinderMismatch Name Name Name Name
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
  -- A cached rendezvous carrier is not source authority. A successful Core
  -- close must also match the checked source endpoint/request identities
  -- and restricted payload binders. Roles, processes and revision are still
  -- explicit external inputs; no display-spelling authority is inferred.
  let expectedRequest = SendReceiveRendezvous
        (ProcessRendezvousSide senderProcess
          (grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint sender))
          senderEndpoint revision senderRole)
        (ProcessRendezvousSide receiverProcess
          (grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint receiver))
          receiverEndpoint revision receiverRole)
      actualRequest = restrictedSourceRequest rendezvous
  if actualRequest == expectedRequest
    then Right ()
    else Left (RestrictedSourceCloseRequestMismatch expectedRequest actualRequest)
  let transfer = restrictedSourceTransfer rendezvous
      sourcePayload = grammarV1ResolvedBinderCoreName
        (checkedComponentSendPayload sender)
      sourceReceived = grammarV1ResolvedBinderCoreName
        (checkedComponentReceivePayload receiver)
      actualPayload = restrictedMessageSenderName transfer
      actualReceived = restrictedMessageReceiverName transfer
  if actualPayload == sourcePayload && actualReceived == sourceReceived
    then Right ()
    else Left (RestrictedSourceCloseTransferBinderMismatch
      sourcePayload sourceReceived actualPayload actualReceived)
  pure GrammarV1RestrictedSourceCloseTransition
    { restrictedSourceClosedSender = senderEndpoint
    , restrictedSourceClosedReceiver = receiverEndpoint
    , restrictedSourceCloseNext = afterReceiver
    }


-- | A restricted send/receive terminal-order diamond, not a new close
-- authority. Unlike the cached-carrier close adapter above, this operation
-- RECHECKS the parsed source pair and the original live activation-derived
-- Core predecessor through the production restricted rendezvous checker.
-- Both End outcomes, protocol instance and process/role identities are
-- independent inputs. The receiver keeps ownership of the transferred
-- restricted payload: endpoint closure is not payload disposition.
data GrammarV1RestrictedSourceCloseDiamondError
  = RestrictedSourceCloseDiamondRendezvousError GrammarV1RestrictedSourceError
  | RestrictedSourceCloseDiamondForwardError GrammarV1RestrictedSourceCloseError
  | RestrictedSourceCloseDiamondReceiverFirstError ProcessEndpointClosureError
  | RestrictedSourceCloseDiamondSenderSecondError ProcessEndpointClosureError
  | RestrictedSourceCloseDiamondDivergentState
  deriving (Eq, Show)

data GrammarV1RestrictedSourceCloseDiamondTransition =
  GrammarV1RestrictedSourceCloseDiamondTransition
    { restrictedSourceDiamondRendezvous :: GrammarV1RestrictedSourceTransition
    , restrictedSourceDiamondForward :: GrammarV1RestrictedSourceCloseTransition
    , restrictedSourceDiamondReceiverFirst :: ProcessCommunicationState
    , restrictedSourceDiamondReverse :: ProcessCommunicationState
    }
  deriving (Eq, Show)

-- | Partial judgment for the admitted two-statement Grammar-v1
-- send/close and receive/close fragment with externally authorized End
-- outcomes:
--
--   source + original Σ0 -- send/receive (restricted) --> Σ1
--   Σ1 -- sender End --> Σs -- receiver End --> Σsr
--   Σ1 -- receiver End --> Σr -- sender End --> Σrs
--   accept iff Σsr == Σrs, comparing ALL Core protocol contexts,
--   resource collections and activation owner occurrences.
--
-- Each actual Core close consumes its own live successor. Any source,
-- rendezvous, close, or equality error returns a precise Left with NO
-- successful state. This says nothing about arbitrary interleavings,
-- automatic process disposal, root closure, or universal refinement.
grammarV1CheckRestrictedSourceCloseDiamond
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
  -> Outcome
  -> Outcome
  -> Either GrammarV1RestrictedSourceCloseDiamondError
       GrammarV1RestrictedSourceCloseDiamondTransition
grammarV1CheckRestrictedSourceCloseDiamond
    staticContext senderRoot senderSource receiverRoot receiverSource
    instanceValue senderRole receiverRole senderProcess receiverProcess
    payloadOccurrence network predecessor senderOutcome receiverOutcome = do
  rendezvous <- mapLeft RestrictedSourceCloseDiamondRendezvousError $
    grammarV1CheckRestrictedSourceRendezvous
      staticContext senderRoot senderSource receiverRoot receiverSource
      instanceValue senderRole receiverRole senderProcess receiverProcess
      payloadOccurrence network predecessor
  let revision = binaryProtocolInstanceRevision instanceValue
  forward <- mapLeft RestrictedSourceCloseDiamondForwardError $
    grammarV1CheckRestrictedSourceClose
      senderRoot senderSource receiverRoot receiverSource
      network rendezvous senderProcess receiverProcess revision
      senderRole receiverRole senderOutcome receiverOutcome
  afterReceiver <- mapLeft RestrictedSourceCloseDiamondReceiverFirstError $
    closeProcessEndpointState network (restrictedSourceNext rendezvous)
      receiverProcess (restrictedSourceClosedReceiver forward)
      revision receiverRole receiverOutcome
  afterBoth <- mapLeft RestrictedSourceCloseDiamondSenderSecondError $
    closeProcessEndpointState network afterReceiver
      senderProcess (restrictedSourceClosedSender forward)
      revision senderRole senderOutcome
  if afterBoth == restrictedSourceCloseNext forward
    then Right GrammarV1RestrictedSourceCloseDiamondTransition
      { restrictedSourceDiamondRendezvous = rendezvous
      , restrictedSourceDiamondForward = forward
      , restrictedSourceDiamondReceiverFirst = afterReceiver
      , restrictedSourceDiamondReverse = afterBoth
      }
    else Left RestrictedSourceCloseDiamondDivergentState


-- | Non-normative FSEM-02 finite observation of exact source-derived
-- predecessor/successor ownership, retained payload and endpoint retirement.
-- All nominal occurrence keys and terminal outcomes are EXTERNAL inputs.
-- The checker replays the original source and original live predecessor; a
-- supplied cached transition is never accepted as source authority.
data GrammarV1RestrictedSourceSuccessorTraceError
  = RestrictedSuccessorTraceDiamondError GrammarV1RestrictedSourceCloseDiamondError
  | RestrictedSuccessorTraceAliasedOccurrence
  | RestrictedSuccessorTracePredecessorMismatch
      ActivationOccurrenceKey (ProcessKey, Name) (Maybe (ProcessKey, Name))
  | RestrictedSuccessorTraceRendezvousOwnerMismatch
  | RestrictedSuccessorTraceTerminalOwnerMismatch
  deriving (Eq, Show)

data GrammarV1RestrictedSourceSuccessorTrace =
  GrammarV1RestrictedSourceSuccessorTrace
    { restrictedSuccessorTraceDiamond :: GrammarV1RestrictedSourceCloseDiamondTransition
    , restrictedSuccessorTraceRendezvousOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    , restrictedSuccessorTraceTerminalOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    }
  deriving (Eq, Show)

-- | Source + original communication state -> either a precise rejection or
-- an exact finite owner trace over three DISTINCT externally named endpoint/
-- payload occurrences. The production restricted rendezvous and both Core End
-- close orders are independently re-executed by the diamond adapter.
--
-- Sender/receiver successor identities are taken from CHECKED lexical
-- binders in that replay, not surface spelling or guessed role authority.
-- The full occurrence map must change only at the three modeled keys:
-- endpoints acquire their exact successors, payload transfers to the receiver,
-- and both endpoints are subsequently retired without payload disposal.
-- Every other occurrence (including unrelated affine spectators) is framed.
grammarV1CheckRestrictedSourceSuccessorTrace
  :: StaticContext
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey -> ProtocolRoleKey
  -> ProcessKey -> ProcessKey
  -> ActivationOccurrenceKey -> ActivationOccurrenceKey
  -> ActivationOccurrenceKey
  -> ProcessNetwork -> ProcessCommunicationState
  -> Outcome -> Outcome
  -> Either GrammarV1RestrictedSourceSuccessorTraceError
       GrammarV1RestrictedSourceSuccessorTrace
grammarV1CheckRestrictedSourceSuccessorTrace
    staticContext senderRoot senderSource receiverRoot receiverSource
    instanceValue senderRole receiverRole senderProcess receiverProcess
    senderOccurrence receiverOccurrence payloadOccurrence
    network original senderOutcome receiverOutcome = do
  if senderOccurrence /= receiverOccurrence
      && senderOccurrence /= payloadOccurrence
      && receiverOccurrence /= payloadOccurrence
    then Right ()
    else Left RestrictedSuccessorTraceAliasedOccurrence
  diamond <- mapLeft RestrictedSuccessorTraceDiamondError $
    grammarV1CheckRestrictedSourceCloseDiamond
      staticContext senderRoot senderSource receiverRoot receiverSource
      instanceValue senderRole receiverRole senderProcess receiverProcess
      payloadOccurrence network original senderOutcome receiverOutcome
  let rendezvous = restrictedSourceDiamondRendezvous diamond
      checkedSender = restrictedSourceSend rendezvous
      checkedReceiver = restrictedSourceReceive rendezvous
      transfer = restrictedSourceTransfer rendezvous
      beforeOwners = communicationRestrictedOwners original
      afterOwners = communicationRestrictedOwners (restrictedSourceNext rendezvous)
      finalOwners = communicationRestrictedOwners (restrictedSourceDiamondReverse diamond)
      senderOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint checkedSender)
      receiverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint checkedReceiver)
      senderNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor checkedSender)
      receiverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor checkedReceiver)
      payloadOld = restrictedMessageSenderName transfer
      payloadNext = restrictedMessageReceiverName transfer
      requirePredecessor occurrence expected =
        if Map.lookup occurrence beforeOwners == Just expected
          then Right ()
          else Left (RestrictedSuccessorTracePredecessorMismatch
            occurrence expected (Map.lookup occurrence beforeOwners))
  requirePredecessor senderOccurrence (senderProcess, senderOld)
  requirePredecessor receiverOccurrence (receiverProcess, receiverOld)
  requirePredecessor payloadOccurrence (senderProcess, payloadOld)
  let expectedAfter = Map.insert payloadOccurrence (receiverProcess, payloadNext)
        (Map.insert senderOccurrence (senderProcess, senderNext)
          (Map.insert receiverOccurrence (receiverProcess, receiverNext) beforeOwners))
      expectedFinal = Map.delete senderOccurrence
        (Map.delete receiverOccurrence expectedAfter)
  if afterOwners == expectedAfter
    then Right ()
    else Left RestrictedSuccessorTraceRendezvousOwnerMismatch
  if finalOwners == expectedFinal
      && communicationRestrictedOwners (restrictedSourceCloseNext
           (restrictedSourceDiamondForward diamond)) == expectedFinal
    then Right GrammarV1RestrictedSourceSuccessorTrace
      { restrictedSuccessorTraceDiamond = diamond
      , restrictedSuccessorTraceRendezvousOwners = afterOwners
      , restrictedSuccessorTraceTerminalOwners = finalOwners
      }
    else Left RestrictedSuccessorTraceTerminalOwnerMismatch

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
