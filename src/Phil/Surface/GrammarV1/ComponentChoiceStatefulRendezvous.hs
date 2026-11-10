{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02, non-normative. Source-checked select/offer followed by atomic
-- activation-derived endpoint occurrence ownership progression.
module Phil.Surface.GrammarV1.ComponentChoiceStatefulRendezvous
  ( GrammarV1StatefulChoiceError (..)
  , GrammarV1StatefulChoice (..)
  , grammarV1CheckStatefulSourceChoice
  , GrammarV1StatefulChoiceClientCloseError (..)
  , GrammarV1StatefulChoiceClientClose (..)
  , grammarV1CloseStatefulSourceChoiceClient
  , GrammarV1StatefulChoiceExplicitPeerCloseError (..)
  , GrammarV1StatefulChoiceExplicitPeerClose (..)
  , grammarV1CloseStatefulSourceChoiceExplicitPeer
  , grammarV1CheckSourceChoiceCloseDiamond
  , GrammarV1ChoiceCloseDiamondError (..)
  , GrammarV1ChoiceCloseDiamond (..)
  , GrammarV1ChoiceSourceSuccessorTraceError (..)
  , GrammarV1ChoiceSourceSuccessorTrace (..)
  , grammarV1CheckChoiceSourceSuccessorTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessActivation (ActivationOccurrenceKey)
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError, closeProcessEndpointState )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , checkProcessCommunicationState
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family (BinaryProtocolInstance (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Name, Outcome)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentSelectClose
  ( GrammarV1CheckedComponentSelectClose (..) )
import Phil.Surface.GrammarV1.ComponentOfferReplay
  ( GrammarV1ComponentOfferReplay (..) )
import Phil.Surface.GrammarV1.ComponentChoiceRendezvous
  ( GrammarV1ChoiceRendezvous (..)
  , GrammarV1ChoiceRendezvousError
  , grammarV1CheckJointSourceChoice
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1StatefulChoiceError
  = GrammarV1StatefulChoiceSourceError GrammarV1ChoiceRendezvousError
  | GrammarV1StatefulChoiceOwnerError ProcessRendezvousError
  | GrammarV1StatefulChoiceContextDivergence
  deriving (Eq, Show)

data GrammarV1StatefulChoice = GrammarV1StatefulChoice
  { statefulChoiceSourceReplay :: GrammarV1ChoiceRendezvous
  , statefulChoiceSuccessor :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | The supplied state must originate from communicationStateFromActivation
-- or a previously checked stateful Core transition. No root authority, payload
-- transfer, scheduler choice or nominal identity is invented here.
-- Source replay is a pure precheck. The production stateful joint transition
-- alone changes the owner index; comparison rejects contextual divergence.
grammarV1CheckStatefulSourceChoice
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> Name
  -> Text
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> Either GrammarV1StatefulChoiceError GrammarV1StatefulChoice
grammarV1CheckStatefulSourceChoice clientRoot clientSource offerRoot offerSource
    instanceValue clientRole offerRole clientProcess offerProcess offeredSuccessor
    peerLabel network state = do
  checked <- mapLeft GrammarV1StatefulChoiceSourceError $
    grammarV1CheckJointSourceChoice
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network (communicationProtocolContexts state)
  advanced <- mapLeft GrammarV1StatefulChoiceOwnerError $
    checkProcessCommunicationState instanceValue network state
      (jointChoiceRequest checked)
  if communicationProtocolContexts advanced == jointChoiceContexts checked
    then Right GrammarV1StatefulChoice
      { statefulChoiceSourceReplay = checked
      , statefulChoiceSuccessor = advanced
      }
    else Left GrammarV1StatefulChoiceContextDivergence


-- | The selected client's literal source 'close chosen' is actually executed
-- after a newly checked two-party stateful choice. The server's 'return unit'
-- arm is deliberately NOT interpreted as a peer endpoint close.
data GrammarV1StatefulChoiceClientCloseError
  = GrammarV1StatefulChoiceClientCloseSourceError GrammarV1StatefulChoiceError
  | GrammarV1StatefulChoiceClientCloseCoreError ProcessEndpointClosureError
  deriving (Eq, Show)

data GrammarV1StatefulChoiceClientClose = GrammarV1StatefulChoiceClientClose
  { statefulChoiceClientCloseSourceReplay :: GrammarV1StatefulChoice
  , statefulChoiceClientCloseEndpoint :: Name
  , statefulChoiceClientCloseSuccessor :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | The caller supplies the initial activation-derived communication state,
-- checked instance, roles, process network, peer choice and terminal outcome.
-- Source checking resolves the exact selected successor / close operand.
-- The native Core stateful rendezvous and endpoint close both replay from
-- that input; no cached successor or source-derived nominal/root authority
-- is trusted. A failed close returns no progressed communication state.
grammarV1CloseStatefulSourceChoiceClient
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> Name
  -> Text
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> Outcome
  -> Either GrammarV1StatefulChoiceClientCloseError
       GrammarV1StatefulChoiceClientClose
grammarV1CloseStatefulSourceChoiceClient
    clientRoot clientSource offerRoot offerSource instanceValue
    clientRole offerRole clientProcess offerProcess offeredSuccessor peerLabel
    network initialState outcome = do
  progressed <- mapLeft GrammarV1StatefulChoiceClientCloseSourceError $
    grammarV1CheckStatefulSourceChoice
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network initialState
  let selected = jointChoiceSelectedSource (statefulChoiceSourceReplay progressed)
      clientSuccessor = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
  closed <- mapLeft GrammarV1StatefulChoiceClientCloseCoreError $
    closeProcessEndpointState network (statefulChoiceSuccessor progressed)
      clientProcess clientSuccessor (binaryProtocolInstanceRevision instanceValue)
      clientRole outcome
  pure GrammarV1StatefulChoiceClientClose
    { statefulChoiceClientCloseSourceReplay = progressed
    , statefulChoiceClientCloseEndpoint = clientSuccessor
    , statefulChoiceClientCloseSuccessor = closed
    }

-- | The Server's literal source offer arm returns unit; it does NOT close an
-- End endpoint. This separate, opt-in Core operation requires the caller to
-- supply the Server's independently authorized terminal outcome, process,
-- role and fresh successor. It replays the checked source and Client close
-- from original activated state, then closes only the still-live Server End.
data GrammarV1StatefulChoiceExplicitPeerCloseError
  = GrammarV1StatefulChoiceExplicitPeerClosePriorError GrammarV1StatefulChoiceClientCloseError
  | GrammarV1StatefulChoiceExplicitPeerCloseCoreError ProcessEndpointClosureError
  deriving (Eq, Show)

data GrammarV1StatefulChoiceExplicitPeerClose = GrammarV1StatefulChoiceExplicitPeerClose
  { statefulChoiceExplicitPeerCloseClient :: GrammarV1StatefulChoiceClientClose
  , statefulChoiceExplicitPeerCloseSuccessor :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | A successful result is a Core terminal-pair transition under TWO
-- separately supplied authorizations, not source Server close execution.
-- There is no hidden fallback for unknown heads, owners or wrong outcomes.
-- On any rejection no successor state is exposed to the caller.
grammarV1CloseStatefulSourceChoiceExplicitPeer
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> Name
  -> Text
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> Outcome
  -> Outcome
  -> Either GrammarV1StatefulChoiceExplicitPeerCloseError
       GrammarV1StatefulChoiceExplicitPeerClose
grammarV1CloseStatefulSourceChoiceExplicitPeer
    clientRoot clientSource offerRoot offerSource instanceValue
    clientRole offerRole clientProcess offerProcess offeredSuccessor peerLabel
    network initialState clientOutcome explicitPeerOutcome = do
  clientClosed <- mapLeft GrammarV1StatefulChoiceExplicitPeerClosePriorError $
    grammarV1CloseStatefulSourceChoiceClient
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network initialState clientOutcome
  serverClosed <- mapLeft GrammarV1StatefulChoiceExplicitPeerCloseCoreError $
    closeProcessEndpointState network
      (statefulChoiceClientCloseSuccessor clientClosed)
      offerProcess offeredSuccessor (binaryProtocolInstanceRevision instanceValue)
      offerRole explicitPeerOutcome
  pure GrammarV1StatefulChoiceExplicitPeerClose
    { statefulChoiceExplicitPeerCloseClient = clientClosed
    , statefulChoiceExplicitPeerCloseSuccessor = serverClosed
    }

-- | Only a conditional diamond: the caller grants the same TWO terminal
-- End outcomes independently of the source 'return unit'. The checked
-- select/offer source is replayed from the activation-derived predecessor
-- in each direction. Full native protocol, resource and owner state must
-- agree, not just the list of removed endpoint occurrences.
data GrammarV1ChoiceCloseDiamondError
  = GrammarV1ChoiceCloseDiamondForwardError GrammarV1StatefulChoiceExplicitPeerCloseError
  | GrammarV1ChoiceCloseDiamondSourceError GrammarV1StatefulChoiceError
  | GrammarV1ChoiceCloseDiamondPeerFirstError ProcessEndpointClosureError
  | GrammarV1ChoiceCloseDiamondClientSecondError ProcessEndpointClosureError
  | GrammarV1ChoiceCloseDiamondDivergence
  deriving (Eq, Show)

data GrammarV1ChoiceCloseDiamond = GrammarV1ChoiceCloseDiamond
  { choiceCloseDiamondForward :: GrammarV1StatefulChoiceExplicitPeerClose
  , choiceCloseDiamondPeerFirst :: ProcessCommunicationState
  , choiceCloseDiamondReverse :: ProcessCommunicationState
  }
  deriving (Eq, Show)

-- | This checks one explicit scheduler permutation of independent terminal
-- closes, not arbitrary commutation, fairness, or source-authorized Server
-- disposition. Each close uses the production Core transition. A rejected
-- branch returns its exact class and exposes NO successful successor.
grammarV1CheckSourceChoiceCloseDiamond
  :: DeclarationKey
  -> GrammarV1ComponentDecl
  -> DeclarationKey
  -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> ProcessKey
  -> ProcessKey
  -> Name
  -> Text
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> Outcome
  -> Outcome
  -> Either GrammarV1ChoiceCloseDiamondError GrammarV1ChoiceCloseDiamond
grammarV1CheckSourceChoiceCloseDiamond
    clientRoot clientSource offerRoot offerSource instanceValue
    clientRole offerRole clientProcess offerProcess offeredSuccessor peerLabel
    network initialState clientOutcome peerOutcome = do
  forward <- mapLeft GrammarV1ChoiceCloseDiamondForwardError $
    grammarV1CloseStatefulSourceChoiceExplicitPeer
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor peerLabel
      network initialState clientOutcome peerOutcome
  checked <- mapLeft GrammarV1ChoiceCloseDiamondSourceError $
    grammarV1CheckStatefulSourceChoice
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network initialState
  let selected = jointChoiceSelectedSource (statefulChoiceSourceReplay checked)
      clientSuccessor = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
      revision = binaryProtocolInstanceRevision instanceValue
  peerFirst <- mapLeft GrammarV1ChoiceCloseDiamondPeerFirstError $
    closeProcessEndpointState network (statefulChoiceSuccessor checked)
      offerProcess offeredSuccessor revision offerRole peerOutcome
  reverseResult <- mapLeft GrammarV1ChoiceCloseDiamondClientSecondError $
    closeProcessEndpointState network peerFirst
      clientProcess clientSuccessor revision clientRole clientOutcome
  if reverseResult == statefulChoiceExplicitPeerCloseSuccessor forward
    then Right GrammarV1ChoiceCloseDiamond
      { choiceCloseDiamondForward = forward
      , choiceCloseDiamondPeerFirst = peerFirst
      , choiceCloseDiamondReverse = reverseResult
      }
    else Left GrammarV1ChoiceCloseDiamondDivergence

-- | Bounded source-select/offer predecessor -> successor -> two-End owner
-- trace. The chosen label, offered successor, occurrence identities, protocol
-- instance/roles, activation and BOTH End authorizations remain caller inputs.
-- A Server return-unit offer arm is NOT a source endpoint-close statement.
data GrammarV1ChoiceSourceSuccessorTraceError
  = ChoiceSourceTraceAliasedOccurrence
  | ChoiceSourceTraceDiamondError GrammarV1ChoiceCloseDiamondError
  | ChoiceSourceTracePredecessorMismatch
      ActivationOccurrenceKey (ProcessKey, Name) (Maybe (ProcessKey, Name))
  | ChoiceSourceTraceProgressionOwnerMismatch
  | ChoiceSourceTraceClientFirstPrefixOwnerMismatch
  | ChoiceSourceTracePeerFirstPrefixOwnerMismatch
  | ChoiceSourceTraceTerminalOwnerMismatch
  deriving (Eq, Show)

data GrammarV1ChoiceSourceSuccessorTrace =
  GrammarV1ChoiceSourceSuccessorTrace
    { choiceSourceTraceDiamond :: GrammarV1ChoiceCloseDiamond
    , choiceSourceTraceReadyOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    , choiceSourceTraceAfterClientOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    , choiceSourceTraceAfterPeerOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    , choiceSourceTraceTerminalOwners ::
        Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    }
  deriving (Eq, Show)

-- | Partial, non-normative FSEM-02 judgment. Reparse/check BOTH component
-- sources and replay the true Core select/offer, then both independently
-- authorized End close orders from the ORIGINAL communication predecessor.
-- No cached transition is accepted as source authority.
--
-- Require the two distinct externally supplied occurrence keys to identify
-- the exact old source-rooted endpoint binders. The Client successor comes
-- from the checked select/close source. The Server successor is an explicit
-- external input checked by the existing Core transition, NOT fabricated
-- from its return-unit offer arm. All other owners must be preserved.
-- Rejection gives a precise Left with no successful progressed state.
grammarV1CheckChoiceSourceSuccessorTrace
  :: DeclarationKey -> GrammarV1ComponentDecl
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey -> ProtocolRoleKey
  -> ProcessKey -> ProcessKey
  -> ActivationOccurrenceKey -> ActivationOccurrenceKey
  -> Name -> Text -> ProcessNetwork -> ProcessCommunicationState
  -> Outcome -> Outcome
  -> Either GrammarV1ChoiceSourceSuccessorTraceError
       GrammarV1ChoiceSourceSuccessorTrace
grammarV1CheckChoiceSourceSuccessorTrace
    clientRoot clientSource offerRoot offerSource instanceValue
    clientRole offerRole clientProcess offerProcess
    clientOccurrence offerOccurrence offeredSuccessor peerLabel network
    original clientOutcome peerOutcome = do
  if clientOccurrence /= offerOccurrence
    then Right ()
    else Left ChoiceSourceTraceAliasedOccurrence
  diamond <- mapLeft ChoiceSourceTraceDiamondError $
    grammarV1CheckSourceChoiceCloseDiamond
      clientRoot clientSource offerRoot offerSource instanceValue
      clientRole offerRole clientProcess offerProcess offeredSuccessor
      peerLabel network original clientOutcome peerOutcome
  let progressed = statefulChoiceClientCloseSourceReplay
        (statefulChoiceExplicitPeerCloseClient (choiceCloseDiamondForward diamond))
      replay = statefulChoiceSourceReplay progressed
      selected = jointChoiceSelectedSource replay
      offered = jointChoiceCheckedOffer replay
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectEndpoint selected)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
      offerOld = grammarV1ResolvedBinderCoreName
        (replayedComponentOfferSourceEndpoint offered)
      beforeOwners = communicationRestrictedOwners original
      readyOwners = communicationRestrictedOwners (statefulChoiceSuccessor progressed)
      afterClientOwners = communicationRestrictedOwners $
        statefulChoiceClientCloseSuccessor
          (statefulChoiceExplicitPeerCloseClient (choiceCloseDiamondForward diamond))
      afterPeerOwners = communicationRestrictedOwners (choiceCloseDiamondPeerFirst diamond)
      finalOwners = communicationRestrictedOwners (choiceCloseDiamondReverse diamond)
      checkPredecessor occurrence expected =
        if Map.lookup occurrence beforeOwners == Just expected
          then Right ()
          else Left (ChoiceSourceTracePredecessorMismatch
            occurrence expected (Map.lookup occurrence beforeOwners))
  checkPredecessor clientOccurrence (clientProcess, clientOld)
  checkPredecessor offerOccurrence (offerProcess, offerOld)
  let expectedReady = Map.insert offerOccurrence (offerProcess, offeredSuccessor)
        (Map.insert clientOccurrence (clientProcess, clientNext) beforeOwners)
      expectedAfterClient = Map.delete clientOccurrence expectedReady
      expectedAfterPeer = Map.delete offerOccurrence expectedReady
      expectedFinal = Map.delete clientOccurrence expectedAfterPeer
  if readyOwners == expectedReady
    then Right ()
    else Left ChoiceSourceTraceProgressionOwnerMismatch
  -- Verify each actual one-sided native End prefix independently.
  if afterClientOwners == expectedAfterClient
    then Right ()
    else Left ChoiceSourceTraceClientFirstPrefixOwnerMismatch
  if afterPeerOwners == expectedAfterPeer
    then Right ()
    else Left ChoiceSourceTracePeerFirstPrefixOwnerMismatch
  if finalOwners == expectedFinal
      && communicationRestrictedOwners
           (statefulChoiceExplicitPeerCloseSuccessor
             (choiceCloseDiamondForward diamond)) == expectedFinal
    then Right GrammarV1ChoiceSourceSuccessorTrace
      { choiceSourceTraceDiamond = diamond
      , choiceSourceTraceReadyOwners = readyOwners
      , choiceSourceTraceAfterClientOwners = afterClientOwners
      , choiceSourceTraceAfterPeerOwners = afterPeerOwners
      , choiceSourceTraceTerminalOwners = finalOwners
      }
    else Left ChoiceSourceTraceTerminalOwnerMismatch

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
