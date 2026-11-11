-- FSEM-02 NON-NORMATIVE: exact typed terminal-head observation following an
-- independently parsed restricted send/receive and the production Core step.
-- All protocol, activation, role, terminal and message authority is external.
module Phil.Surface.GrammarV1.ComponentRestrictedTerminalHead
  ( GrammarV1RestrictedTerminalHeadError (..)
  , GrammarV1RestrictedTerminalHeadTrace (..)
  , grammarV1CheckRestrictedTerminalHeadTrace
  , GrammarV1RestrictedTypedPrefixError (..)
  , GrammarV1RestrictedTypedPrefixTrace (..)
  , grammarV1CheckRestrictedTypedPrefixTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Process (ProcessKey, ProcessNetwork)
import Phil.Core.ProcessActivation (ActivationOccurrenceKey)
import Phil.Core.ProcessRendezvous (ProcessCommunicationState (..))
import Phil.Core.Protocol
  ( ProtocolContext (..), ProtocolEndpointBinding (..), ProtocolRoleKey )
import Phil.Core.Protocol.Family (BinaryProtocolInstance)
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Name, Outcome, Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentReceiveClose
  ( GrammarV1CheckedComponentReceiveClose (..) )
import Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
  ( GrammarV1RestrictedSourceError
  , GrammarV1RestrictedSourceTransition (..)
  , grammarV1CheckRestrictedSourceRendezvous
  )
import Phil.Surface.GrammarV1.ComponentRestrictedSourceClose
  ( GrammarV1RestrictedClosePrefixError
  , GrammarV1RestrictedClosePrefixes (..)
  , GrammarV1RestrictedSourceSuccessorTrace (..)
  , GrammarV1RestrictedSourceCloseDiamondTransition (..)
  , grammarV1CheckRestrictedSourceClosePrefixes
  )
import Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1CheckedComponentSendClose (..) )
import Phil.Surface.GrammarV1.Parser (GrammarV1ComponentDecl)

data GrammarV1RestrictedTerminalHeadError
  = RestrictedTerminalHeadSourceError GrammarV1RestrictedSourceError
  | RestrictedTerminalHeadProcessMissing ProcessKey
  | RestrictedTerminalHeadPredecessorMissing ProcessKey Name
  | RestrictedTerminalHeadPredecessorResourceMismatch ProcessKey Name
  | RestrictedTerminalHeadWrongAction ProcessKey Name Session
  | RestrictedTerminalHeadOutcomeMismatch ProcessKey Name Outcome Outcome
  | RestrictedTerminalHeadPredecessorNotConsumed ProcessKey Name
  | RestrictedTerminalHeadSuccessorMismatch ProcessKey Name
  | RestrictedTerminalHeadSuccessorResourceMismatch ProcessKey Name
  deriving (Eq, Show)

data GrammarV1RestrictedTerminalHeadTrace =
  GrammarV1RestrictedTerminalHeadTrace
    { restrictedTerminalHeadSourceStep :: GrammarV1RestrictedSourceTransition
    , restrictedTerminalHeadSenderSuccessor :: ProtocolEndpointBinding
    , restrictedTerminalHeadReceiverSuccessor :: ProtocolEndpointBinding
    }
  deriving (Eq, Show)

data HeadAction = HeadSend | HeadReceive

-- | A finite terminal-continuation competence slice, not a rule for all
-- sessions. Exact Send/Receive predecessors must independently continue to
-- the externally supplied End outcomes; no alternative head is coerced.
-- On success, the actual Core successor must retire each predecessor,
-- preserve each nominal instance/role binding, and install exactly the
-- corresponding TyEndpoint (End outcome) linear resource.
-- Failure produces no state. Source close statements are NOT executed here.
grammarV1CheckRestrictedTerminalHeadTrace
  :: StaticContext
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> BinaryProtocolInstance
  -> ProtocolRoleKey -> ProtocolRoleKey
  -> ProcessKey -> ProcessKey -> ActivationOccurrenceKey
  -> ProcessNetwork -> ProcessCommunicationState
  -> Outcome -> Outcome
  -> Either GrammarV1RestrictedTerminalHeadError GrammarV1RestrictedTerminalHeadTrace
grammarV1CheckRestrictedTerminalHeadTrace
    staticContext senderRoot senderSource receiverRoot receiverSource
    instanceValue senderRole receiverRole senderProcess receiverProcess
    payloadOccurrence network before senderEnd receiverEnd = do
  step <- mapLeft RestrictedTerminalHeadSourceError $
    grammarV1CheckRestrictedSourceRendezvous
      staticContext senderRoot senderSource receiverRoot receiverSource
      instanceValue senderRole receiverRole senderProcess receiverProcess
      payloadOccurrence network before
  let send = restrictedSourceSend step
      recv = restrictedSourceReceive step
      senderOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint send)
      senderNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor send)
      receiverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint recv)
      receiverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor recv)
      after = restrictedSourceNext step
  senderBinding <- observe HeadSend senderProcess senderOld senderNext senderEnd before after
  receiverBinding <- observe HeadReceive receiverProcess receiverOld receiverNext receiverEnd before after
  pure GrammarV1RestrictedTerminalHeadTrace
    { restrictedTerminalHeadSourceStep = step
    , restrictedTerminalHeadSenderSuccessor = senderBinding
    , restrictedTerminalHeadReceiverSuccessor = receiverBinding
    }

observe
  :: HeadAction -> ProcessKey -> Name -> Name -> Outcome
  -> ProcessCommunicationState -> ProcessCommunicationState
  -> Either GrammarV1RestrictedTerminalHeadError ProtocolEndpointBinding
observe action process old next expectedOutcome before after = do
  oldContext <- requireContext process before
  nextContext <- requireContext process after
  oldBinding <- maybe
    (Left (RestrictedTerminalHeadPredecessorMissing process old))
    Right (Map.lookup old (protocolEndpoints oldContext))
  if Map.lookup old (linearBindings (protocolResources oldContext))
       == Just (TyEndpoint (protocolEndpointSession oldBinding))
    then Right ()
    else Left (RestrictedTerminalHeadPredecessorResourceMismatch process old)
  case (action, protocolEndpointSession oldBinding) of
    (HeadSend, Send _ _ (End actual)) -> requireOutcome actual
    (HeadReceive, Receive _ _ (End actual)) -> requireOutcome actual
    (_, observed) -> Left (RestrictedTerminalHeadWrongAction process old observed)
  if Map.notMember old (protocolEndpoints nextContext)
       && Map.notMember old (linearBindings (protocolResources nextContext))
    then Right ()
    else Left (RestrictedTerminalHeadPredecessorNotConsumed process old)
  let expectedBinding = oldBinding
        { protocolEndpointName = next
        , protocolEndpointSession = End expectedOutcome
        }
  actualBinding <- maybe
    (Left (RestrictedTerminalHeadSuccessorMismatch process next))
    Right (Map.lookup next (protocolEndpoints nextContext))
  if actualBinding == expectedBinding
    then Right ()
    else Left (RestrictedTerminalHeadSuccessorMismatch process next)
  if Map.lookup next (linearBindings (protocolResources nextContext))
       == Just (TyEndpoint (End expectedOutcome))
    then Right actualBinding
    else Left (RestrictedTerminalHeadSuccessorResourceMismatch process next)
  where
    requireOutcome actual
      | actual == expectedOutcome = Right ()
      | otherwise = Left
          (RestrictedTerminalHeadOutcomeMismatch process old actual expectedOutcome)

requireContext
  :: ProcessKey -> ProcessCommunicationState
  -> Either GrammarV1RestrictedTerminalHeadError ProtocolContext
requireContext process state =
  maybe (Left (RestrictedTerminalHeadProcessMissing process)) Right
    (Map.lookup process (communicationProtocolContexts state))


-- | NON-NORMATIVE FSEM-02 composition: the independently replayed *typed*
-- terminal Send/Receive head check must agree exactly with the full source/
-- Core owner-ledger replay through EITHER authorized first End closure.
-- A successful checked source statement does not grant terminal authority.
data GrammarV1RestrictedTypedPrefixError
  = RestrictedTypedPrefixHeadError GrammarV1RestrictedTerminalHeadError
  | RestrictedTypedPrefixLedgerError GrammarV1RestrictedClosePrefixError
  | RestrictedTypedPrefixRendezvousMismatch
  | RestrictedTypedPrefixSenderFirstMismatch
  | RestrictedTypedPrefixReceiverFirstMismatch
  deriving (Eq, Show)

data GrammarV1RestrictedTypedPrefixTrace = GrammarV1RestrictedTypedPrefixTrace
  { restrictedTypedPrefixHeads :: GrammarV1RestrictedTerminalHeadTrace
  , restrictedTypedPrefixOwners :: GrammarV1RestrictedClosePrefixes
  } deriving (Eq, Show)

-- | Explicit pre-state, authorized protocol/network, distinct endpoint and
-- payload occurrence keys, and two supplied End outcomes are mandatory.
-- Rejects the source/Core head mismatch before attempting either close.
-- Replays the source from the ORIGINAL state a second independent time:
-- typed head success cannot be validated against a cached ledger.
-- The complete Core rendezvous states must agree, not just their projections.
-- At each one-sided prefix, the opposite typed End endpoint remains live and
-- the retired endpoint is absent in BOTH protocol and linear resource maps.
-- The underlying owner-prefix checker separately validates the complete
-- occurrence ledger, transferred payload and all affine spectators.
grammarV1CheckRestrictedTypedPrefixTrace
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
  -> Either GrammarV1RestrictedTypedPrefixError GrammarV1RestrictedTypedPrefixTrace
grammarV1CheckRestrictedTypedPrefixTrace
    staticContext senderRoot senderSource receiverRoot receiverSource
    instanceValue senderRole receiverRole senderProcess receiverProcess
    senderOccurrence receiverOccurrence payloadOccurrence
    network before senderOutcome receiverOutcome = do
  heads <- mapLeft RestrictedTypedPrefixHeadError $
    grammarV1CheckRestrictedTerminalHeadTrace
      staticContext senderRoot senderSource receiverRoot receiverSource
      instanceValue senderRole receiverRole senderProcess receiverProcess
      payloadOccurrence network before senderOutcome receiverOutcome
  prefixes <- mapLeft RestrictedTypedPrefixLedgerError $
    grammarV1CheckRestrictedSourceClosePrefixes
      staticContext senderRoot senderSource receiverRoot receiverSource
      instanceValue senderRole receiverRole senderProcess receiverProcess
      senderOccurrence receiverOccurrence payloadOccurrence
      network before senderOutcome receiverOutcome
  let headStep = restrictedTerminalHeadSourceStep heads
      ledgerStep = restrictedSourceDiamondRendezvous
        (restrictedSuccessorTraceDiamond (restrictedClosePrefixTrace prefixes))
      senderEnd = restrictedTerminalHeadSenderSuccessor heads
      receiverEnd = restrictedTerminalHeadReceiverSuccessor heads
      senderContext = Map.lookup senderProcess . communicationProtocolContexts
      receiverContext = Map.lookup receiverProcess . communicationProtocolContexts
      senderFirst = restrictedClosePrefixSenderFirst prefixes
      receiverFirst = restrictedClosePrefixReceiverFirst prefixes
      stillLive endpoint context =
        Map.lookup (protocolEndpointName endpoint) (protocolEndpoints context)
          == Just endpoint
        && Map.lookup (protocolEndpointName endpoint)
             (linearBindings (protocolResources context))
          == Just (TyEndpoint (protocolEndpointSession endpoint))
      retired endpoint context =
        Map.notMember (protocolEndpointName endpoint) (protocolEndpoints context)
        && Map.notMember (protocolEndpointName endpoint)
             (linearBindings (protocolResources context))
  if headStep == ledgerStep
    then Right ()
    else Left RestrictedTypedPrefixRendezvousMismatch
  case (senderContext senderFirst, receiverContext senderFirst) of
    (Just sender, Just receiver)
      | retired senderEnd sender && stillLive receiverEnd receiver -> Right ()
    _ -> Left RestrictedTypedPrefixSenderFirstMismatch
  case (senderContext receiverFirst, receiverContext receiverFirst) of
    (Just sender, Just receiver)
      | stillLive senderEnd sender && retired receiverEnd receiver -> Right ()
    _ -> Left RestrictedTypedPrefixReceiverFirstMismatch
  pure GrammarV1RestrictedTypedPrefixTrace
    { restrictedTypedPrefixHeads = heads
    , restrictedTypedPrefixOwners = prefixes
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
