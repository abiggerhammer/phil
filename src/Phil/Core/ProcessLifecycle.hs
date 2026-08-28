{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessLifecycle
  ( ProcessTerminalFact (..)
  , RootTerminalFact (..)
  , ProcessRuntimeStatus (..)
  , FatalProcessTransition (..)
  , DeclaredTerminalTransition (..)
  , EnabledProcessTransition (..)
  , RootClosureState (..)
  , ProcessNetworkDisposition (..)
  , ProcessRuntimeState (..)
  , ProcessLifecycleError (..)
  , initializeProcessRuntime
  , initializeProcessRuntimeWithObligations
  , applyFatalProcessTransition
  , applyDeclaredTerminalTransition
  , validateFatalProcessLocality
  , classifyProcessNetwork
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError
  , ensureComplete
  , useBinding
  )
import Phil.Core.Process
  ( ActivationStatus (..)
  , ProcessKey
  , ProcessNetwork (..)
  , ProcessOccurrence (..)
  )
import Phil.Core.Protocol
  ( ProtocolContext (..)
  )
import Phil.Core.Syntax
  ( Control (..)
  , Mode (..)
  , Name
  , ObligationId
  )

data ProcessTerminalFact = ProcessTerminalFact
  { terminalFactProcess :: ProcessKey
  , terminalFactControl :: Control
  }
  deriving (Eq, Show)

data RootTerminalFact = RootTerminalFact
  { rootTerminalProcesses :: Map.Map ProcessKey ProcessTerminalFact
  }
  deriving (Eq, Show)

data ProcessRuntimeStatus
  = ProcessRunning
  | ProcessTerminal ProcessTerminalFact
  deriving (Eq, Show)

-- | A fatal transition may dispose only resources explicitly named here. The
-- checker derives the actor's successor context mechanically; peer state is not
-- an input to the transition and therefore cannot be silently cancelled or
-- cleaned up.
data FatalProcessTransition = FatalProcessTransition
  { fatalTransitionProcess :: ProcessKey
  , fatalTransitionClass :: Text
  , fatalTransitionDetail :: Text
  , fatalTransitionDisposals :: [Name]
  }
  deriving (Eq, Show)

-- | An ordinary declared terminal transition. The transition cannot discharge
-- assurance obligations itself: all process-local residual obligations must
-- already have an accepted disposition before this transition may construct a
-- ProcessTerminalFact.
data DeclaredTerminalTransition = DeclaredTerminalTransition
  { declaredTerminalProcess :: ProcessKey
  , declaredTerminalControl :: Control
  , declaredTerminalDisposals :: [Name]
  }
  deriving (Eq, Show)

-- | Source-semantic enabledness used only to distinguish a live network that
-- can still step from one that is stuck. This is not a fairness or progress
-- claim and does not select a scheduler.
data EnabledProcessTransition
  = EnabledLocalStep ProcessKey
  | EnabledRendezvousStep ProcessKey ProcessKey
  deriving (Eq, Ord, Show)

-- | Exact root-level residue that must be closed after every process has a
-- local terminal fact. These are semantic root residues, not target/runtime
-- cleanup facts.
data RootClosureState = RootClosureState
  { rootOpenResources :: Set.Set Name
  , rootOpenObligations :: Set.Set ObligationId
  , rootPendingObservables :: Set.Set Text
  }
  deriving (Eq, Show)

data ProcessNetworkDisposition
  = NetworkCanStep
  | NetworkStuck (Set.Set ProcessKey)
  | NetworkTerminal RootTerminalFact
  deriving (Eq, Show)

data ProcessRuntimeState = ProcessRuntimeState
  { runtimeNetwork :: ProcessNetwork
  , runtimeProtocolContexts :: Map.Map ProcessKey ProtocolContext
  , runtimeStatuses :: Map.Map ProcessKey ProcessRuntimeStatus
  , runtimeOpenObligations :: Map.Map ProcessKey (Set.Set ObligationId)
  }
  deriving (Eq, Show)

data ProcessLifecycleError
  = RuntimeUnknownProcess ProcessKey
  | RuntimeProcessNotActive ProcessKey ActivationStatus
  | RuntimeMissingProtocolContext ProcessKey
  | RuntimeUnexpectedProtocolContext ProcessKey
  | RuntimeUnexpectedObligationContext ProcessKey
  | RuntimeProcessAlreadyTerminal ProcessKey ProcessTerminalFact
  | DuplicateFatalDisposal Name
  | FatalDisposalUnknown ProcessKey Name CheckError
  | FatalDisposalUnrestricted ProcessKey Name
  | FatalTerminalResourceError ProcessKey CheckError
  | FatalTerminalLiveEndpoints ProcessKey [Name]
  | FatalTerminalOpenObligations ProcessKey (Set.Set ObligationId)
  | TerminalContinueRejected ProcessKey
  | DuplicateTerminalDisposal Name
  | TerminalDisposalUnknown ProcessKey Name CheckError
  | TerminalDisposalUnrestricted ProcessKey Name
  | TerminalResourceError ProcessKey CheckError
  | TerminalLiveEndpoints ProcessKey [Name]
  | TerminalOpenObligations ProcessKey (Set.Set ObligationId)
  | FatalSuccessorNetworkChanged
  | FatalSuccessorProcessSetChanged
  | FatalActorNotTerminal ProcessKey
  | FatalActorControlMismatch ProcessKey Control
  | FatalPeerStatusChanged ProcessKey ProcessRuntimeStatus ProcessRuntimeStatus
  | FatalPeerContextChanged ProcessKey ProtocolContext ProtocolContext
  | FatalPeerObligationsChanged
      ProcessKey
      (Set.Set ObligationId)
      (Set.Set ObligationId)
  | EnabledTransitionUnknownProcess ProcessKey
  | EnabledTransitionTerminalProcess ProcessKey ProcessTerminalFact
  | EnabledRendezvousSameProcess ProcessKey
  | RootTerminalOpenResources (Set.Set Name)
  | RootTerminalOpenObligations (Set.Set ObligationId)
  | RootTerminalPendingObservables (Set.Set Text)
  deriving (Eq, Show)

initializeProcessRuntime
  :: ProcessNetwork
  -> Map.Map ProcessKey ProtocolContext
  -> Either ProcessLifecycleError ProcessRuntimeState
initializeProcessRuntime network contexts =
  initializeProcessRuntimeWithObligations network contexts Map.empty

initializeProcessRuntimeWithObligations
  :: ProcessNetwork
  -> Map.Map ProcessKey ProtocolContext
  -> Map.Map ProcessKey (Set.Set ObligationId)
  -> Either ProcessLifecycleError ProcessRuntimeState
initializeProcessRuntimeWithObligations network contexts obligations = do
  mapM_ requireActiveOccurrence (Map.toList (processNetworkPopulation network))
  mapM_ requireContextForPopulation (Map.keys (processNetworkPopulation network))
  case Set.lookupMin unexpectedContexts of
    Just processKey -> Left (RuntimeUnexpectedProtocolContext processKey)
    Nothing -> Right ()
  case Set.lookupMin unexpectedObligationContexts of
    Just processKey -> Left (RuntimeUnexpectedObligationContext processKey)
    Nothing -> Right ProcessRuntimeState
      { runtimeNetwork = network
      , runtimeProtocolContexts = contexts
      , runtimeStatuses = Map.map (const ProcessRunning) (processNetworkPopulation network)
      , runtimeOpenObligations = Map.fromSet obligationsFor populationKeys
      }
  where
    populationKeys = Map.keysSet (processNetworkPopulation network)
    unexpectedContexts = Map.keysSet contexts `Set.difference` populationKeys
    unexpectedObligationContexts = Map.keysSet obligations `Set.difference` populationKeys
    obligationsFor processKey = Map.findWithDefault Set.empty processKey obligations

    requireActiveOccurrence (processKey, occurrence) =
      case processOccurrenceActivation occurrence of
        Active -> Right ()
        status -> Left (RuntimeProcessNotActive processKey status)

    requireContextForPopulation processKey
      | Map.member processKey contexts = Right ()
      | otherwise = Left (RuntimeMissingProtocolContext processKey)

applyFatalProcessTransition
  :: FatalProcessTransition
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ProcessRuntimeState
applyFatalProcessTransition transition state = do
  let processKey = fatalTransitionProcess transition
  ensureRunning processKey state
  context <- requireRuntimeContext state processKey
  disposed <- disposeFatalExplicitly processKey (fatalTransitionDisposals transition) context
  mapLeft (FatalTerminalResourceError processKey) $
    ensureComplete (protocolResources disposed)
  if Map.null (protocolEndpoints disposed)
    then Right ()
    else Left (FatalTerminalLiveEndpoints processKey (Map.keys (protocolEndpoints disposed)))
  openObligations <- requireOpenObligations state processKey
  if Set.null openObligations
    then Right ()
    else Left (FatalTerminalOpenObligations processKey openObligations)
  let control = Failed (fatalTransitionClass transition) (fatalTransitionDetail transition)
      fact = ProcessTerminalFact processKey control
      successor = state
        { runtimeProtocolContexts = Map.insert processKey disposed (runtimeProtocolContexts state)
        , runtimeStatuses = Map.insert processKey (ProcessTerminal fact) (runtimeStatuses state)
        }
  validateFatalProcessLocality processKey state successor
  pure successor

applyDeclaredTerminalTransition
  :: DeclaredTerminalTransition
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ProcessRuntimeState
applyDeclaredTerminalTransition transition state = do
  let processKey = declaredTerminalProcess transition
      control = declaredTerminalControl transition
  ensureRunning processKey state
  case control of
    Continue -> Left (TerminalContinueRejected processKey)
    _ -> Right ()
  context <- requireRuntimeContext state processKey
  disposed <- disposeTerminalExplicitly processKey (declaredTerminalDisposals transition) context
  mapLeft (TerminalResourceError processKey) $
    ensureComplete (protocolResources disposed)
  if Map.null (protocolEndpoints disposed)
    then Right ()
    else Left (TerminalLiveEndpoints processKey (Map.keys (protocolEndpoints disposed)))
  openObligations <- requireOpenObligations state processKey
  if Set.null openObligations
    then Right ()
    else Left (TerminalOpenObligations processKey openObligations)
  let fact = ProcessTerminalFact processKey control
  pure state
    { runtimeProtocolContexts = Map.insert processKey disposed (runtimeProtocolContexts state)
    , runtimeStatuses = Map.insert processKey (ProcessTerminal fact) (runtimeStatuses state)
    }

validateFatalProcessLocality
  :: ProcessKey
  -> ProcessRuntimeState
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ()
validateFatalProcessLocality actor before after = do
  if runtimeNetwork before == runtimeNetwork after
    then Right ()
    else Left FatalSuccessorNetworkChanged
  if sameProcessDomains
    then Right ()
    else Left FatalSuccessorProcessSetChanged
  afterActor <- requireStatus after actor
  case afterActor of
    ProcessTerminal fact ->
      case terminalFactControl fact of
        Failed _ _ -> Right ()
        other -> Left (FatalActorControlMismatch actor other)
    ProcessRunning -> Left (FatalActorNotTerminal actor)
  mapM_ validatePeer peerKeys
  where
    sameProcessDomains =
      Map.keysSet (runtimeStatuses before) == Map.keysSet (runtimeStatuses after)
        && Map.keysSet (runtimeProtocolContexts before) == Map.keysSet (runtimeProtocolContexts after)
        && Map.keysSet (runtimeOpenObligations before) == Map.keysSet (runtimeOpenObligations after)
    peerKeys = filter (/= actor) (Map.keys (runtimeStatuses before))

    validatePeer processKey = do
      beforeStatus <- requireStatus before processKey
      afterStatus <- requireStatus after processKey
      if beforeStatus == afterStatus
        then Right ()
        else Left (FatalPeerStatusChanged processKey beforeStatus afterStatus)
      beforeContext <- requireRuntimeContext before processKey
      afterContext <- requireRuntimeContext after processKey
      if beforeContext == afterContext
        then Right ()
        else Left (FatalPeerContextChanged processKey beforeContext afterContext)
      beforeObligations <- requireOpenObligations before processKey
      afterObligations <- requireOpenObligations after processKey
      if beforeObligations == afterObligations
        then Right ()
        else Left (FatalPeerObligationsChanged processKey beforeObligations afterObligations)

classifyProcessNetwork
  :: RootClosureState
  -> [EnabledProcessTransition]
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ProcessNetworkDisposition
classifyProcessNetwork rootClosure enabled state = do
  mapM_ (validateEnabledTransition state) enabled
  let activeProcesses = Set.fromList
        [ processKey
        | (processKey, ProcessRunning) <- Map.toList (runtimeStatuses state)
        ]
  if Set.null activeProcesses
    then NetworkTerminal <$> closeRoot rootClosure state
    else if null enabled
      then Right (NetworkStuck activeProcesses)
      else Right NetworkCanStep

closeRoot
  :: RootClosureState
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError RootTerminalFact
closeRoot rootClosure state = do
  if Set.null (rootOpenResources rootClosure)
    then Right ()
    else Left (RootTerminalOpenResources (rootOpenResources rootClosure))
  if Set.null (rootOpenObligations rootClosure)
    then Right ()
    else Left (RootTerminalOpenObligations (rootOpenObligations rootClosure))
  if Set.null (rootPendingObservables rootClosure)
    then Right ()
    else Left (RootTerminalPendingObservables (rootPendingObservables rootClosure))
  facts <- mapM requireTerminalFact (Map.toList (runtimeStatuses state))
  pure RootTerminalFact
    { rootTerminalProcesses = Map.fromList facts
    }
  where
    requireTerminalFact (processKey, status) =
      case status of
        ProcessTerminal fact -> Right (processKey, fact)
        ProcessRunning -> Left (FatalActorNotTerminal processKey)

validateEnabledTransition
  :: ProcessRuntimeState
  -> EnabledProcessTransition
  -> Either ProcessLifecycleError ()
validateEnabledTransition state enabled =
  case enabled of
    EnabledLocalStep processKey -> requireRunning processKey
    EnabledRendezvousStep left right
      | left == right -> Left (EnabledRendezvousSameProcess left)
      | otherwise -> requireRunning left >> requireRunning right
  where
    requireRunning processKey =
      case Map.lookup processKey (runtimeStatuses state) of
        Nothing -> Left (EnabledTransitionUnknownProcess processKey)
        Just ProcessRunning -> Right ()
        Just (ProcessTerminal fact) -> Left (EnabledTransitionTerminalProcess processKey fact)

ensureRunning
  :: ProcessKey
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ()
ensureRunning processKey state = do
  status <- maybe
    (Left (RuntimeUnknownProcess processKey))
    Right
    (Map.lookup processKey (runtimeStatuses state))
  case status of
    ProcessRunning -> Right ()
    ProcessTerminal fact -> Left (RuntimeProcessAlreadyTerminal processKey fact)

requireStatus
  :: ProcessRuntimeState
  -> ProcessKey
  -> Either ProcessLifecycleError ProcessRuntimeStatus
requireStatus state processKey =
  maybe (Left (RuntimeUnknownProcess processKey)) Right
    (Map.lookup processKey (runtimeStatuses state))

requireRuntimeContext
  :: ProcessRuntimeState
  -> ProcessKey
  -> Either ProcessLifecycleError ProtocolContext
requireRuntimeContext state processKey =
  maybe (Left (RuntimeMissingProtocolContext processKey)) Right
    (Map.lookup processKey (runtimeProtocolContexts state))

requireOpenObligations
  :: ProcessRuntimeState
  -> ProcessKey
  -> Either ProcessLifecycleError (Set.Set ObligationId)
requireOpenObligations state processKey =
  maybe (Left (RuntimeUnknownProcess processKey)) Right
    (Map.lookup processKey (runtimeOpenObligations state))

disposeFatalExplicitly
  :: ProcessKey
  -> [Name]
  -> ProtocolContext
  -> Either ProcessLifecycleError ProtocolContext
disposeFatalExplicitly processKey names context = go Set.empty context names
  where
    go _ current [] = Right current
    go seen current (name : rest)
      | Set.member name seen = Left (DuplicateFatalDisposal name)
      | otherwise = do
          (mode, _, resources) <- mapLeft (FatalDisposalUnknown processKey name) $
            useBinding name (protocolResources current)
          case mode of
            Unrestricted -> Left (FatalDisposalUnrestricted processKey name)
            Affine -> continue resources
            Linear -> continue resources
      where
        continue resources =
          go
            (Set.insert name seen)
            (current
              { protocolResources = resources
              , protocolEndpoints = Map.delete name (protocolEndpoints current)
              })
            rest

disposeTerminalExplicitly
  :: ProcessKey
  -> [Name]
  -> ProtocolContext
  -> Either ProcessLifecycleError ProtocolContext
disposeTerminalExplicitly processKey names context = go Set.empty context names
  where
    go _ current [] = Right current
    go seen current (name : rest)
      | Set.member name seen = Left (DuplicateTerminalDisposal name)
      | otherwise = do
          (mode, _, resources) <- mapLeft (TerminalDisposalUnknown processKey name) $
            useBinding name (protocolResources current)
          case mode of
            Unrestricted -> Left (TerminalDisposalUnrestricted processKey name)
            Affine -> continue resources
            Linear -> continue resources
      where
        continue resources =
          go
            (Set.insert name seen)
            (current
              { protocolResources = resources
              , protocolEndpoints = Map.delete name (protocolEndpoints current)
              })
            rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
