{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessLifecycle
  ( ProcessTerminalFact (..)
  , ProcessRuntimeStatus (..)
  , FatalProcessTransition (..)
  , ProcessRuntimeState (..)
  , ProcessLifecycleError (..)
  , initializeProcessRuntime
  , applyFatalProcessTransition
  , validateFatalProcessLocality
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
  )

data ProcessTerminalFact = ProcessTerminalFact
  { terminalFactProcess :: ProcessKey
  , terminalFactControl :: Control
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

data ProcessRuntimeState = ProcessRuntimeState
  { runtimeNetwork :: ProcessNetwork
  , runtimeProtocolContexts :: Map.Map ProcessKey ProtocolContext
  , runtimeStatuses :: Map.Map ProcessKey ProcessRuntimeStatus
  }
  deriving (Eq, Show)

data ProcessLifecycleError
  = RuntimeUnknownProcess ProcessKey
  | RuntimeProcessNotActive ProcessKey ActivationStatus
  | RuntimeMissingProtocolContext ProcessKey
  | RuntimeUnexpectedProtocolContext ProcessKey
  | RuntimeProcessAlreadyTerminal ProcessKey ProcessTerminalFact
  | DuplicateFatalDisposal Name
  | FatalDisposalUnknown ProcessKey Name CheckError
  | FatalDisposalUnrestricted ProcessKey Name
  | FatalTerminalResourceError ProcessKey CheckError
  | FatalTerminalLiveEndpoints ProcessKey [Name]
  | FatalSuccessorNetworkChanged
  | FatalSuccessorProcessSetChanged
  | FatalActorNotTerminal ProcessKey
  | FatalActorControlMismatch ProcessKey Control
  | FatalPeerStatusChanged ProcessKey ProcessRuntimeStatus ProcessRuntimeStatus
  | FatalPeerContextChanged ProcessKey ProtocolContext ProtocolContext
  deriving (Eq, Show)

initializeProcessRuntime
  :: ProcessNetwork
  -> Map.Map ProcessKey ProtocolContext
  -> Either ProcessLifecycleError ProcessRuntimeState
initializeProcessRuntime network contexts = do
  mapM_ requireActiveOccurrence (Map.toList (processNetworkPopulation network))
  mapM_ requireContextForPopulation (Map.keys (processNetworkPopulation network))
  case Set.lookupMin unexpectedContexts of
    Just processKey -> Left (RuntimeUnexpectedProtocolContext processKey)
    Nothing -> Right ProcessRuntimeState
      { runtimeNetwork = network
      , runtimeProtocolContexts = contexts
      , runtimeStatuses = Map.map (const ProcessRunning) (processNetworkPopulation network)
      }
  where
    populationKeys = Map.keysSet (processNetworkPopulation network)
    unexpectedContexts = Map.keysSet contexts `Set.difference` populationKeys

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
  status <- maybe
    (Left (RuntimeUnknownProcess processKey))
    Right
    (Map.lookup processKey (runtimeStatuses state))
  case status of
    ProcessRunning -> Right ()
    ProcessTerminal fact -> Left (RuntimeProcessAlreadyTerminal processKey fact)
  context <- maybe
    (Left (RuntimeMissingProtocolContext processKey))
    Right
    (Map.lookup processKey (runtimeProtocolContexts state))
  disposed <- disposeExplicitly processKey (fatalTransitionDisposals transition) context
  mapLeft (FatalTerminalResourceError processKey) $
    ensureComplete (protocolResources disposed)
  if Map.null (protocolEndpoints disposed)
    then Right ()
    else Left (FatalTerminalLiveEndpoints processKey (Map.keys (protocolEndpoints disposed)))
  let control = Failed (fatalTransitionClass transition) (fatalTransitionDetail transition)
      fact = ProcessTerminalFact processKey control
      successor = state
        { runtimeProtocolContexts = Map.insert processKey disposed (runtimeProtocolContexts state)
        , runtimeStatuses = Map.insert processKey (ProcessTerminal fact) (runtimeStatuses state)
        }
  validateFatalProcessLocality processKey state successor
  pure successor

validateFatalProcessLocality
  :: ProcessKey
  -> ProcessRuntimeState
  -> ProcessRuntimeState
  -> Either ProcessLifecycleError ()
validateFatalProcessLocality actor before after = do
  if runtimeNetwork before == runtimeNetwork after
    then Right ()
    else Left FatalSuccessorNetworkChanged
  if Map.keysSet (runtimeStatuses before) == Map.keysSet (runtimeStatuses after)
      && Map.keysSet (runtimeProtocolContexts before) == Map.keysSet (runtimeProtocolContexts after)
    then Right ()
    else Left FatalSuccessorProcessSetChanged
  afterActor <- maybe
    (Left (RuntimeUnknownProcess actor))
    Right
    (Map.lookup actor (runtimeStatuses after))
  case afterActor of
    ProcessTerminal fact ->
      case terminalFactControl fact of
        Failed _ _ -> Right ()
        other -> Left (FatalActorControlMismatch actor other)
    ProcessRunning -> Left (FatalActorNotTerminal actor)
  mapM_ validatePeer peerKeys
  where
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

disposeExplicitly
  :: ProcessKey
  -> [Name]
  -> ProtocolContext
  -> Either ProcessLifecycleError ProtocolContext
disposeExplicitly processKey names context = go Set.empty context names
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
