-- Non-normative FSEM-02: compose the checked source rendezvous/close
-- prefix with *existing* process/root terminal checks. Terminal control,
-- explicit disposals, assurance dispositions and root residues are external
-- obligations, not permissions invented from source syntax.
module Phil.Surface.GrammarV1.ComponentRestrictedSourceTerminal
  ( GrammarV1RestrictedSourceTerminalError (..)
  , GrammarV1RestrictedSourceTerminalTransition (..)
  , grammarV1CheckRestrictedSourceTerminal
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Process (ProcessKey, ProcessNetwork (..))
import Phil.Core.ProcessActivation (ActivationOccurrenceKey)
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError, closeProcessEndpointState )
import Phil.Core.ProcessLifecycle
  ( DeclaredTerminalTransition (..)
  , ProcessLifecycleError
  , ProcessNetworkDisposition (..)
  , ProcessRuntimeState
  , RootClosureState
  , RootTerminalFact
  , applyDeclaredTerminalTransition
  , classifyProcessNetwork
  , initializeProcessRuntimeWithObligations
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , RestrictedMessageTransfer (..)
  , ProcessRendezvousError
  , checkRestrictedProcessRendezvous
  )
import Phil.Core.Protocol.Family (BinaryProtocolInstance)
import Phil.Core.Syntax (Control (..), Name, ObligationId, Outcome)
import Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
  ( GrammarV1RestrictedSourceTransition (..))
import Phil.Surface.GrammarV1.ComponentRestrictedSourceClose
  ( GrammarV1RestrictedSourceCloseTransition (..))

data GrammarV1RestrictedSourceTerminalError
  = RestrictedSourceTerminalNotSendReceive
  | RestrictedSourceTerminalProcessMismatch ProcessKey ProcessKey
  | RestrictedSourceTerminalUnexpectedPopulation
  | RestrictedSourceTerminalCloseIdentityMismatch
  | RestrictedSourceTerminalCloseReplaySenderError ProcessEndpointClosureError
  | RestrictedSourceTerminalCloseReplayReceiverError ProcessEndpointClosureError
  | RestrictedSourceTerminalCloseStateMismatch
  | RestrictedSourceTerminalRendezvousReplayError ProcessRendezvousError
  | RestrictedSourceTerminalRendezvousStateMismatch
  | RestrictedSourceTerminalWrongControl ProcessKey Control Outcome
  | RestrictedSourceTerminalPayloadOwnerMismatch
      ActivationOccurrenceKey (Maybe (ProcessKey, Name))
  | RestrictedSourceTerminalOwnerUnknown ProcessKey Name
  | RestrictedSourceTerminalOwnerAmbiguous
      ProcessKey Name [ActivationOccurrenceKey]
  | RestrictedSourceTerminalUnaccountedOwner
      ActivationOccurrenceKey ProcessKey Name
  | RestrictedSourceTerminalInitializeError ProcessLifecycleError
  | RestrictedSourceTerminalSenderError ProcessLifecycleError
  | RestrictedSourceTerminalReceiverError ProcessLifecycleError
  | RestrictedSourceTerminalRootError ProcessLifecycleError
  | RestrictedSourceTerminalNotTerminal ProcessNetworkDisposition
  deriving (Eq, Show)

data GrammarV1RestrictedSourceTerminalTransition =
  GrammarV1RestrictedSourceTerminalTransition
    { restrictedSourceTerminalRuntime :: ProcessRuntimeState
    , restrictedSourceTerminalFact :: RootTerminalFact
    , restrictedSourceTerminalRemainingOwners
        :: Map.Map ActivationOccurrenceKey (ProcessKey, Name)
    }
  deriving (Eq, Show)

-- | Bounded conditional judgment:
--   checked source send/receive; checked source close;
--   explicit two-process activation; caller-provided terminal dispositions,
--   obligation map and root residues
--     -> terminal or an exact rejection with no successor.
--
-- This is NOT a source-language disposal statement or general architecture
-- interpreter. The source prefix has already been checked by the production
-- Surface adapters. The caller must independently authorize terminal control,
-- all disposal names, process obligations and root closure. The native Core
-- lifecycle checker checks the actual *post-close* resource/protocol contexts.
-- The activation owner index is reconciled by exact (process, name) lookup
-- and every remaining restricted owner must be explicitly disposed. The
-- claimed post-close communication state must match independently replayed
-- native Core close transitions, not merely the two source binder names. No
-- Source-protocol authority and the full activation-derived predecessor
-- are external inputs. Both Core rendezvous and close replays must agree
-- exactly with the cached carriers before terminal admission.
-- network/root terminal fact is returned on any failure.
grammarV1CheckRestrictedSourceTerminal
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1RestrictedSourceTransition
  -> GrammarV1RestrictedSourceCloseTransition
  -> DeclaredTerminalTransition
  -> DeclaredTerminalTransition
  -> Outcome
  -> Outcome
  -> Map.Map ProcessKey (Set.Set ObligationId)
  -> RootClosureState
  -> Either GrammarV1RestrictedSourceTerminalError
       GrammarV1RestrictedSourceTerminalTransition
grammarV1CheckRestrictedSourceTerminal
    instanceValue network predecessor rendezvous closed senderTerminal receiverTerminal
    senderOutcome receiverOutcome obligations root = do
  (senderSide, receiverSide) <- case restrictedSourceRequest rendezvous of
    SendReceiveRendezvous sender receiver -> Right (sender, receiver)
    _ -> Left RestrictedSourceTerminalNotSendReceive
  let senderProcess = rendezvousProcess senderSide
      receiverProcess = rendezvousProcess receiverSide
      senderDeclared = declaredTerminalProcess senderTerminal
      receiverDeclared = declaredTerminalProcess receiverTerminal
      closedState = restrictedSourceCloseNext closed
      owners = communicationRestrictedOwners closedState
      transfer = restrictedSourceTransfer rendezvous
      payloadOccurrence = restrictedMessageOccurrence transfer
      payloadOwner = (receiverProcess, restrictedMessageReceiverName transfer)
  if senderDeclared == senderProcess
    then Right ()
    else Left (RestrictedSourceTerminalProcessMismatch senderProcess senderDeclared)
  if receiverDeclared == receiverProcess
    then Right ()
    else Left (RestrictedSourceTerminalProcessMismatch receiverProcess receiverDeclared)
  if senderProcess /= receiverProcess
      && Map.keysSet (processNetworkPopulation network)
          == Set.fromList [senderProcess, receiverProcess]
    then Right ()
    else Left RestrictedSourceTerminalUnexpectedPopulation
  if restrictedSourceClosedSender closed == rendezvousSuccessor senderSide
      && restrictedSourceClosedReceiver closed == rendezvousSuccessor receiverSide
    then Right ()
    else Left RestrictedSourceTerminalCloseIdentityMismatch
  requireClosed senderProcess senderOutcome (declaredTerminalControl senderTerminal)
  requireClosed receiverProcess receiverOutcome (declaredTerminalControl receiverTerminal)
  if Map.lookup payloadOccurrence owners == Just payloadOwner
    then Right ()
    else Left (RestrictedSourceTerminalPayloadOwnerMismatch payloadOccurrence
                (Map.lookup payloadOccurrence owners))
  -- A successful source-close carrier must agree with independently
  -- re-executing both native End transitions on the exact pre-close Core
  -- state. Checking only binder names and a payload owner would otherwise
  -- let a forged carrier smuggle a different resource or endpoint context
  -- into the lifecycle/root terminal checker.
  afterSenderClose <- mapLeft RestrictedSourceTerminalCloseReplaySenderError $
    closeProcessEndpointState network (restrictedSourceNext rendezvous)
      senderProcess (rendezvousSuccessor senderSide)
      (rendezvousInstance senderSide) (rendezvousRole senderSide) senderOutcome
  replayedClosed <- mapLeft RestrictedSourceTerminalCloseReplayReceiverError $
    closeProcessEndpointState network afterSenderClose
      receiverProcess (rendezvousSuccessor receiverSide)
      (rendezvousInstance receiverSide) (rendezvousRole receiverSide) receiverOutcome
  if closedState == replayedClosed
    then Right ()
    else Left RestrictedSourceTerminalCloseStateMismatch
  -- Re-execute the actual restricted rendezvous from its independently
  -- supplied activation-derived predecessor and protocol authority.
  -- A cached successor is not itself provenance evidence: require full
  -- protocol/resource-context and owner-occurrence equality.
  replayedRendezvous <- mapLeft RestrictedSourceTerminalRendezvousReplayError $
    checkRestrictedProcessRendezvous instanceValue network predecessor
      (restrictedSourceRequest rendezvous)
      (restrictedSourceTransfer rendezvous)
  if restrictedSourceNext rendezvous == replayedRendezvous
    then Right ()
    else Left RestrictedSourceTerminalRendezvousStateMismatch
  -- Next the real lifecycle/resource/obligation transitions. Reconciliation
  -- does not turn a Core rejection into success or mutate rejected states.
  initialized <- mapLeft RestrictedSourceTerminalInitializeError $
    initializeProcessRuntimeWithObligations network
      (communicationProtocolContexts closedState) obligations
  afterSender <- mapLeft RestrictedSourceTerminalSenderError $
    applyDeclaredTerminalTransition senderTerminal initialized
  afterReceiver <- mapLeft RestrictedSourceTerminalReceiverError $
    applyDeclaredTerminalTransition receiverTerminal afterSender
  afterOwners <- retireOwners owners
    ([(senderProcess, n) | n <- declaredTerminalDisposals senderTerminal]
       ++ [(receiverProcess, n) | n <- declaredTerminalDisposals receiverTerminal])
  case Map.toAscList afterOwners of
    ((key, (process, name)) : _) ->
      Left (RestrictedSourceTerminalUnaccountedOwner key process name)
    [] -> Right ()
  disposition <- mapLeft RestrictedSourceTerminalRootError $
    classifyProcessNetwork root [] afterReceiver
  case disposition of
    NetworkTerminal fact -> Right GrammarV1RestrictedSourceTerminalTransition
      { restrictedSourceTerminalRuntime = afterReceiver
      , restrictedSourceTerminalFact = fact
      , restrictedSourceTerminalRemainingOwners = afterOwners
      }
    other -> Left (RestrictedSourceTerminalNotTerminal other)
  where
    requireClosed process outcome control
      | control == Closed outcome = Right ()
      | otherwise = Left (RestrictedSourceTerminalWrongControl process control outcome)

retireOwners
  :: Map.Map ActivationOccurrenceKey (ProcessKey, Name)
  -> [(ProcessKey, Name)]
  -> Either GrammarV1RestrictedSourceTerminalError
       (Map.Map ActivationOccurrenceKey (ProcessKey, Name))
retireOwners owners [] = Right owners
retireOwners owners ((process, name) : rest) =
  case [key | (key, owner) <- Map.toAscList owners
            , owner == (process, name)] of
    [] -> Left (RestrictedSourceTerminalOwnerUnknown process name)
    [key] -> retireOwners (Map.delete key owners) rest
    keys -> Left (RestrictedSourceTerminalOwnerAmbiguous process name keys)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
