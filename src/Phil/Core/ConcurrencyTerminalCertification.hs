module Phil.Core.ConcurrencyTerminalCertification
  ( CertifiedTerminalRuntime
  , certifiedTerminalRuntimeState
  , CertifiedTerminalEnabledStep
  , CertifiedTerminalDisposition
  , certifiedTerminalDispositionNative
  , ProcessTerminalKernelFacts (..)
  , FailureIsolationKernelFacts (..)
  , RootTerminalKernelFacts (..)
  , NetworkStuckKernelFacts (..)
  , ConcurrencyTerminalCertificationError (..)
  , initializeCertifiedTerminalRuntime
  , certifyEnabledLocalStep
  , certifyEnabledRendezvousStep
  , verifyProcessTerminalKernelFacts
  , verifyFailureIsolationKernelFacts
  , verifyRootTerminalKernelFacts
  , verifyNetworkStuckKernelFacts
  , applyDeclaredTerminalTransitionCertified
  , applyFatalProcessTransitionCertified
  , classifyProcessNetworkCertified
  ) where

import qualified ConcurrencyTerminalKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.ConcurrencyRendezvousCertification
  ( CertifiedRendezvousActivation
  , CertifiedRendezvousResult
  , certifiedRendezvousActivationNetwork
  , certifiedRendezvousCausality
  , certifiedRendezvousReceiverProcess
  , certifiedRendezvousSenderProcess
  )
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.ProcessLifecycle
  ( DeclaredTerminalTransition (..)
  , EnabledProcessTransition (..)
  , FatalProcessTransition (..)
  , ProcessLifecycleError
  , ProcessNetworkDisposition (..)
  , ProcessRuntimeState (..)
  , ProcessRuntimeStatus (..)
  , ProcessTerminalFact (..)
  , RootClosureState (..)
  , RootTerminalFact (..)
  , applyDeclaredTerminalTransition
  , applyFatalProcessTransition
  , classifyProcessNetwork
  , initializeProcessRuntimeWithObligations
  )
import Phil.Core.Protocol (ProtocolContext (..))
import Phil.Core.Syntax (Control (..), ObligationId)

newtype CertifiedTerminalRuntime = CertifiedTerminalRuntime
  { unCertifiedTerminalRuntime :: ProcessRuntimeState
  }
  deriving (Eq, Show)

certifiedTerminalRuntimeState :: CertifiedTerminalRuntime -> ProcessRuntimeState
certifiedTerminalRuntimeState = unCertifiedTerminalRuntime

newtype CertifiedTerminalEnabledStep = CertifiedTerminalEnabledStep
  { terminalEnabledNative :: EnabledProcessTransition
  }
  deriving (Eq, Show)

newtype CertifiedTerminalDisposition = CertifiedTerminalDisposition
  { certifiedTerminalDispositionNative :: ProcessNetworkDisposition
  }
  deriving (Eq, Show)

data ProcessTerminalKernelFacts = ProcessTerminalKernelFacts
  { terminalResourcesClosed :: Bool
  , terminalObligationsClosed :: Bool
  , terminalEndpointsClosed :: Bool
  , terminalControlExact :: Bool
  }
  deriving (Eq, Show)

data FailureIsolationKernelFacts = FailureIsolationKernelFacts
  { failureActorWasRunning :: Bool
  , failureActorBecomesFailed :: Bool
  , failurePeersUnchanged :: Bool
  }
  deriving (Eq, Show)

data RootTerminalKernelFacts = RootTerminalKernelFacts
  { terminalRootResourcesClosed :: Bool
  , terminalRootObligationsClosed :: Bool
  , terminalRootObservablesClosed :: Bool
  , terminalFactsComplete :: Bool
  , terminalNoInventedFacts :: Bool
  , terminalAllStaticStatusesTerminated :: Bool
  }
  deriving (Eq, Show)

data NetworkStuckKernelFacts = NetworkStuckKernelFacts
  { stuckRootNotTerminal :: Bool
  , stuckRunningStaticProcess :: Bool
  , stuckNoEnabledSemanticStep :: Bool
  }
  deriving (Eq, Show)

data ConcurrencyTerminalCertificationError
  = ConcurrencyTerminalNativeError ProcessLifecycleError
  | ConcurrencyTerminalRuntimeInvariant
  | ConcurrencyTerminalDeclaredIsolationDisagreement ProcessKey
  | ConcurrencyTerminalProcessKernelDisagreement ProcessTerminalKernelFacts
  | ConcurrencyTerminalFailureKernelDisagreement FailureIsolationKernelFacts
  | ConcurrencyTerminalRootKernelDisagreement RootTerminalKernelFacts
  | ConcurrencyTerminalStuckKernelDisagreement NetworkStuckKernelFacts
  | ConcurrencyTerminalEnabledLocalStepInvalid ProcessKey
  | ConcurrencyTerminalEnabledRendezvousInvalid ProcessKey ProcessKey
  | ConcurrencyTerminalDispositionInvariant ProcessNetworkDisposition
  deriving (Eq, Show)

initializeCertifiedTerminalRuntime
  :: CertifiedRendezvousActivation
  -> Map.Map ProcessKey ProtocolContext
  -> Map.Map ProcessKey (Set.Set ObligationId)
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalRuntime
initializeCertifiedTerminalRuntime activation contexts obligations = do
  let network = certifiedRendezvousActivationNetwork activation
  state <- mapLeft ConcurrencyTerminalNativeError $
    initializeProcessRuntimeWithObligations network contexts obligations
  if runtimeInvariant state && runtimeNetwork state == network
    then Right (CertifiedTerminalRuntime state)
    else Left ConcurrencyTerminalRuntimeInvariant

certifyEnabledLocalStep
  :: CertifiedTerminalRuntime
  -> ProcessKey
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalEnabledStep
certifyEnabledLocalStep runtime processKey
  | processIsRunningStatic state processKey =
      Right (CertifiedTerminalEnabledStep (EnabledLocalStep processKey))
  | otherwise = Left (ConcurrencyTerminalEnabledLocalStepInvalid processKey)
  where
    state = certifiedTerminalRuntimeState runtime

certifyEnabledRendezvousStep
  :: CertifiedTerminalRuntime
  -> CertifiedRendezvousResult
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalEnabledStep
certifyEnabledRendezvousStep runtime rendezvous
  | sender /= receiver
      && processIsRunningStatic state sender
      && processIsRunningStatic state receiver =
      Right (CertifiedTerminalEnabledStep (EnabledRendezvousStep sender receiver))
  | otherwise = Left (ConcurrencyTerminalEnabledRendezvousInvalid sender receiver)
  where
    state = certifiedTerminalRuntimeState runtime
    causality = certifiedRendezvousCausality rendezvous
    sender = certifiedRendezvousSenderProcess causality
    receiver = certifiedRendezvousReceiverProcess causality

verifyProcessTerminalKernelFacts
  :: ProcessTerminalKernelFacts
  -> Either ConcurrencyTerminalCertificationError ()
verifyProcessTerminalKernelFacts facts
  | Kernel.decideCertifiedProcessTerminalByFacts
      (terminalResourcesClosed facts)
      (terminalObligationsClosed facts)
      (terminalEndpointsClosed facts)
      (terminalControlExact facts) = Right ()
  | otherwise = Left (ConcurrencyTerminalProcessKernelDisagreement facts)

verifyFailureIsolationKernelFacts
  :: FailureIsolationKernelFacts
  -> Either ConcurrencyTerminalCertificationError ()
verifyFailureIsolationKernelFacts facts
  | Kernel.decideExactFailureIsolationByFacts
      (failureActorWasRunning facts)
      (failureActorBecomesFailed facts)
      (failurePeersUnchanged facts) = Right ()
  | otherwise = Left (ConcurrencyTerminalFailureKernelDisagreement facts)

verifyRootTerminalKernelFacts
  :: RootTerminalKernelFacts
  -> Either ConcurrencyTerminalCertificationError ()
verifyRootTerminalKernelFacts facts
  | Kernel.decideCertifiedRootTerminalByFacts
      (terminalRootResourcesClosed facts)
      (terminalRootObligationsClosed facts)
      (terminalRootObservablesClosed facts)
      (terminalFactsComplete facts)
      (terminalNoInventedFacts facts)
      (terminalAllStaticStatusesTerminated facts) = Right ()
  | otherwise = Left (ConcurrencyTerminalRootKernelDisagreement facts)

verifyNetworkStuckKernelFacts
  :: NetworkStuckKernelFacts
  -> Either ConcurrencyTerminalCertificationError ()
verifyNetworkStuckKernelFacts facts
  | Kernel.decideCertifiedNetworkStuckByFacts
      (stuckRootNotTerminal facts)
      (stuckRunningStaticProcess facts)
      (stuckNoEnabledSemanticStep facts) = Right ()
  | otherwise = Left (ConcurrencyTerminalStuckKernelDisagreement facts)

applyDeclaredTerminalTransitionCertified
  :: DeclaredTerminalTransition
  -> CertifiedTerminalRuntime
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalRuntime
applyDeclaredTerminalTransitionCertified transition runtime = do
  let before = certifiedTerminalRuntimeState runtime
      actor = declaredTerminalProcess transition
      expectedControl = declaredTerminalControl transition
  after <- mapLeft ConcurrencyTerminalNativeError $
    applyDeclaredTerminalTransition transition before
  if runtimeInvariant after
    then Right ()
    else Left ConcurrencyTerminalRuntimeInvariant
  if transitionIsLocal actor before after
    then Right ()
    else Left (ConcurrencyTerminalDeclaredIsolationDisagreement actor)
  verifyProcessTerminalKernelFacts
    (processTerminalKernelFacts actor expectedControl after)
  pure (CertifiedTerminalRuntime after)

applyFatalProcessTransitionCertified
  :: FatalProcessTransition
  -> CertifiedTerminalRuntime
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalRuntime
applyFatalProcessTransitionCertified transition runtime = do
  let before = certifiedTerminalRuntimeState runtime
      actor = fatalTransitionProcess transition
      expectedControl = Failed
        (fatalTransitionClass transition)
        (fatalTransitionDetail transition)
  after <- mapLeft ConcurrencyTerminalNativeError $
    applyFatalProcessTransition transition before
  if runtimeInvariant after
    then Right ()
    else Left ConcurrencyTerminalRuntimeInvariant
  verifyProcessTerminalKernelFacts
    (processTerminalKernelFacts actor expectedControl after)
  verifyFailureIsolationKernelFacts
    (failureIsolationKernelFacts actor before after)
  pure (CertifiedTerminalRuntime after)

classifyProcessNetworkCertified
  :: RootClosureState
  -> [CertifiedTerminalEnabledStep]
  -> CertifiedTerminalRuntime
  -> Either ConcurrencyTerminalCertificationError CertifiedTerminalDisposition
classifyProcessNetworkCertified rootClosure enabled runtime = do
  let state = certifiedTerminalRuntimeState runtime
      nativeEnabled = map terminalEnabledNative enabled
  if runtimeInvariant state
    then Right ()
    else Left ConcurrencyTerminalRuntimeInvariant
  disposition <- mapLeft ConcurrencyTerminalNativeError $
    classifyProcessNetwork rootClosure nativeEnabled state
  case disposition of
    NetworkTerminal fact -> do
      verifyRootTerminalKernelFacts (rootTerminalKernelFacts rootClosure fact state)
      pure (CertifiedTerminalDisposition disposition)
    NetworkStuck active -> do
      let running = runningStaticProcesses state
          facts = NetworkStuckKernelFacts
            { stuckRootNotTerminal = not (Set.null running)
            , stuckRunningStaticProcess = not (Set.null running)
            , stuckNoEnabledSemanticStep = null enabled
            }
      if active == running
        then Right ()
        else Left (ConcurrencyTerminalDispositionInvariant disposition)
      verifyNetworkStuckKernelFacts facts
      pure (CertifiedTerminalDisposition disposition)
    NetworkCanStep
      | null enabled -> Left (ConcurrencyTerminalDispositionInvariant disposition)
      | otherwise -> pure (CertifiedTerminalDisposition disposition)

processTerminalKernelFacts
  :: ProcessKey
  -> Control
  -> ProcessRuntimeState
  -> ProcessTerminalKernelFacts
processTerminalKernelFacts processKey expectedControl state =
  ProcessTerminalKernelFacts
    { terminalResourcesClosed = maybe False resourceClosed context
    , terminalObligationsClosed = maybe False Set.null obligations
    , terminalEndpointsClosed = maybe False (Map.null . protocolEndpoints) context
    , terminalControlExact = case status of
        Just (ProcessTerminal fact) ->
          terminalFactProcess fact == processKey
            && terminalFactControl fact == expectedControl
            && terminalControl expectedControl
        _ -> False
    }
  where
    context = Map.lookup processKey (runtimeProtocolContexts state)
    obligations = Map.lookup processKey (runtimeOpenObligations state)
    status = Map.lookup processKey (runtimeStatuses state)

failureIsolationKernelFacts
  :: ProcessKey
  -> ProcessRuntimeState
  -> ProcessRuntimeState
  -> FailureIsolationKernelFacts
failureIsolationKernelFacts actor before after =
  FailureIsolationKernelFacts
    { failureActorWasRunning =
        Map.lookup actor (runtimeStatuses before) == Just ProcessRunning
    , failureActorBecomesFailed = case Map.lookup actor (runtimeStatuses after) of
        Just (ProcessTerminal fact) ->
          terminalFactProcess fact == actor
            && case terminalFactControl fact of
              Failed _ _ -> True
              _ -> False
        _ -> False
    , failurePeersUnchanged = transitionIsLocal actor before after
    }

rootTerminalKernelFacts
  :: RootClosureState
  -> RootTerminalFact
  -> ProcessRuntimeState
  -> RootTerminalKernelFacts
rootTerminalKernelFacts rootClosure rootFact state =
  RootTerminalKernelFacts
    { terminalRootResourcesClosed = Set.null (rootOpenResources rootClosure)
    , terminalRootObligationsClosed = Set.null (rootOpenObligations rootClosure)
    , terminalRootObservablesClosed = Set.null (rootPendingObservables rootClosure)
    , terminalFactsComplete = all populationFactExact (Map.toList population)
    , terminalNoInventedFacts =
        Map.keysSet facts == Map.keysSet population
          && all embeddedFactExact (Map.toList facts)
    , terminalAllStaticStatusesTerminated =
        all populationStatusTerminal (Map.toList population)
    }
  where
    population = processNetworkPopulation (runtimeNetwork state)
    facts = rootTerminalProcesses rootFact
    populationFactExact (processKey, occurrence) =
      processOccurrenceKey occurrence == processKey
        && case Map.lookup processKey facts of
          Just fact -> terminalFactProcess fact == processKey && terminalControl (terminalFactControl fact)
          Nothing -> False
    embeddedFactExact (processKey, fact) =
      terminalFactProcess fact == processKey && terminalControl (terminalFactControl fact)
    populationStatusTerminal (processKey, occurrence) =
      processOccurrenceKey occurrence == processKey
        && case Map.lookup processKey (runtimeStatuses state) of
          Just (ProcessTerminal fact) ->
            terminalFactProcess fact == processKey && terminalControl (terminalFactControl fact)
          _ -> False

runtimeInvariant :: ProcessRuntimeState -> Bool
runtimeInvariant state =
  not (Map.null population)
    && populationKeys == Map.keysSet (runtimeStatuses state)
    && populationKeys == Map.keysSet (runtimeProtocolContexts state)
    && populationKeys == Map.keysSet (runtimeOpenObligations state)
    && all occurrenceExact (Map.toList population)
    && all terminalStatusExact (Map.toList (runtimeStatuses state))
  where
    population = processNetworkPopulation (runtimeNetwork state)
    populationKeys = Map.keysSet population
    occurrenceExact (processKey, occurrence) =
      processOccurrenceKey occurrence == processKey
        && processOccurrenceActivation occurrence == Active
    terminalStatusExact (processKey, status) = case status of
      ProcessRunning -> True
      ProcessTerminal fact -> terminalFactProcess fact == processKey

transitionIsLocal
  :: ProcessKey
  -> ProcessRuntimeState
  -> ProcessRuntimeState
  -> Bool
transitionIsLocal actor before after =
  runtimeNetwork before == runtimeNetwork after
    && Map.keysSet (runtimeStatuses before) == Map.keysSet (runtimeStatuses after)
    && Map.keysSet (runtimeProtocolContexts before) == Map.keysSet (runtimeProtocolContexts after)
    && Map.keysSet (runtimeOpenObligations before) == Map.keysSet (runtimeOpenObligations after)
    && all peerUnchanged peers
  where
    peers = filter (/= actor) (Map.keys (runtimeStatuses before))
    peerUnchanged processKey =
      Map.lookup processKey (runtimeStatuses before) == Map.lookup processKey (runtimeStatuses after)
        && Map.lookup processKey (runtimeProtocolContexts before) == Map.lookup processKey (runtimeProtocolContexts after)
        && Map.lookup processKey (runtimeOpenObligations before) == Map.lookup processKey (runtimeOpenObligations after)

processIsRunningStatic :: ProcessRuntimeState -> ProcessKey -> Bool
processIsRunningStatic state processKey =
  case ( Map.lookup processKey (processNetworkPopulation (runtimeNetwork state))
       , Map.lookup processKey (runtimeStatuses state)
       ) of
    (Just occurrence, Just ProcessRunning) ->
      processOccurrenceKey occurrence == processKey
        && processOccurrenceActivation occurrence == Active
    _ -> False

runningStaticProcesses :: ProcessRuntimeState -> Set.Set ProcessKey
runningStaticProcesses state = Set.fromList
  [ processKey
  | (processKey, occurrence) <- Map.toList (processNetworkPopulation (runtimeNetwork state))
  , processOccurrenceKey occurrence == processKey
  , processOccurrenceActivation occurrence == Active
  , Map.lookup processKey (runtimeStatuses state) == Just ProcessRunning
  ]

resourceClosed :: ProtocolContext -> Bool
resourceClosed context =
  Set.null (sharedLoans resources)
    && Map.null (linearBindings resources)
  where
    resources = protocolResources context

terminalControl :: Control -> Bool
terminalControl control = case control of
  Closed _ -> True
  Failed _ _ -> True
  Continue -> False
  Return _ -> False

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
