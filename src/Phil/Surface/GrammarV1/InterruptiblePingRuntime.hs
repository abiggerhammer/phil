{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.InterruptiblePingRuntime
  ( GrammarV1InterruptiblePingEvidence (..)
  , GrammarV1InterruptiblePingError (..)
  , grammarV1FinishUnboundedPingOnCancellation
  ) where

import Data.Text (Text)
import Phil.Core.Process
  ( ProcessNetwork
  )
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError
  , closeProcessEndpointState
  )
import Phil.Core.ProcessLifecycle
  ( DeclaredTerminalTransition (..)
  , ProcessLifecycleError
  , ProcessNetworkDisposition (..)
  , RootClosureState (..)
  , RootTerminalFact
  , applyDeclaredTerminalTransition
  , classifyProcessNetwork
  , initializeProcessRuntime
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , checkProcessCommunicationSuccessor
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  )
import Phil.Core.Syntax
  ( Control (..)
  , Name (..)
  , Outcome (..)
  )
import Phil.IO.SignalCancellation
  ( CheckedSignalCancellation
  , HostSignalEvent (..)
  , checkedSignalCancellationEvent
  )
import Phil.Surface.GrammarV1.UnboundedPingRuntime
  ( GrammarV1UnboundedPingRuntimeEvidence (..)
  , GrammarV1UnboundedPingRuntimePlan (..)
  )

data GrammarV1InterruptiblePingEvidence = GrammarV1InterruptiblePingEvidence
  { interruptiblePingCancellation :: CheckedSignalCancellation
  , interruptiblePingClientDoneEndpoint :: Name
  , interruptiblePingServerDoneEndpoint :: Name
  , interruptiblePingTerminalFact :: RootTerminalFact
  }
  deriving (Eq, Show)

data GrammarV1InterruptiblePingError
  = GrammarV1InterruptiblePingUnexpectedCancellation HostSignalEvent
  | GrammarV1InterruptiblePingProcessError ProcessRendezvousError
  | GrammarV1InterruptiblePingClosureError ProcessEndpointClosureError
  | GrammarV1InterruptiblePingLifecycleError ProcessLifecycleError
  | GrammarV1InterruptiblePingNotTerminal ProcessNetworkDisposition
  deriving (Eq, Show)

-- | Consume an explicitly reified SIGINT cancellation at a live recursive Ping
-- backedge.  The checked cancellation does not itself mutate protocol state.
-- Ordinary session semantics selects Done, closes the exact successor endpoints,
-- and only then constructs process/root terminal facts.
grammarV1FinishUnboundedPingOnCancellation
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1UnboundedPingRuntimePlan
  -> GrammarV1UnboundedPingRuntimeEvidence
  -> CheckedSignalCancellation
  -> Either
      GrammarV1InterruptiblePingError
      (ProcessCommunicationState, GrammarV1InterruptiblePingEvidence)
grammarV1FinishUnboundedPingOnCancellation
    instanceValue network communication plan prefixEvidence cancellation = do
  case checkedSignalCancellationEvent cancellation of
    HostSignalSIGINT -> Right ()
    other -> Left (GrammarV1InterruptiblePingUnexpectedCancellation other)

  let clientEndpoint = unboundedPingEvidenceFinalClientEndpoint prefixEvidence
      serverEndpoint = unboundedPingEvidenceFinalServerEndpoint prefixEvidence
      clientDone = doneName clientEndpoint "client"
      serverDone = doneName serverEndpoint "server"
      doneChoice = SelectOfferRendezvous
        (side
          (unboundedPingRuntimeClientProcess plan)
          clientEndpoint
          clientDone
          (unboundedPingRuntimeClientRole plan))
        (side
          (unboundedPingRuntimeServerProcess plan)
          serverEndpoint
          serverDone
          (unboundedPingRuntimeServerRole plan))
        "Done"

  afterDone <- mapLeft GrammarV1InterruptiblePingProcessError $
    checkProcessCommunicationSuccessor
      instanceValue network communication doneChoice

  closedClient <- mapLeft GrammarV1InterruptiblePingClosureError $
    closeProcessEndpointState
      network
      afterDone
      (unboundedPingRuntimeClientProcess plan)
      clientDone
      (unboundedPingRuntimeInstance plan)
      (unboundedPingRuntimeClientRole plan)
      doneOutcome

  closedBoth <- mapLeft GrammarV1InterruptiblePingClosureError $
    closeProcessEndpointState
      network
      closedClient
      (unboundedPingRuntimeServerProcess plan)
      serverDone
      (unboundedPingRuntimeInstance plan)
      (unboundedPingRuntimeServerRole plan)
      doneOutcome

  runtime0 <- mapLeft GrammarV1InterruptiblePingLifecycleError $
    initializeProcessRuntime network (communicationProtocolContexts closedBoth)

  runtime1 <- mapLeft GrammarV1InterruptiblePingLifecycleError $
    applyDeclaredTerminalTransition
      (terminalTransition (unboundedPingRuntimeClientProcess plan))
      runtime0

  runtime2 <- mapLeft GrammarV1InterruptiblePingLifecycleError $
    applyDeclaredTerminalTransition
      (terminalTransition (unboundedPingRuntimeServerProcess plan))
      runtime1

  disposition <- mapLeft GrammarV1InterruptiblePingLifecycleError $
    classifyProcessNetwork emptyRootClosure [] runtime2

  terminalFact <- case disposition of
    NetworkTerminal fact -> Right fact
    other -> Left (GrammarV1InterruptiblePingNotTerminal other)

  Right
    ( closedBoth
    , GrammarV1InterruptiblePingEvidence
        { interruptiblePingCancellation = cancellation
        , interruptiblePingClientDoneEndpoint = clientDone
        , interruptiblePingServerDoneEndpoint = serverDone
        , interruptiblePingTerminalFact = terminalFact
        }
    )
  where
    side process endpoint successor role = ProcessRendezvousSide
      { rendezvousProcess = process
      , rendezvousEndpoint = endpoint
      , rendezvousSuccessor = successor
      , rendezvousInstance = unboundedPingRuntimeInstance plan
      , rendezvousRole = role
      }

    terminalTransition process = DeclaredTerminalTransition
      { declaredTerminalProcess = process
      , declaredTerminalControl = Closed doneOutcome
      , declaredTerminalDisposals = []
      }

doneName :: Name -> Text -> Name
doneName (Name prefix) sideName =
  Name (prefix <> ":int009:sigint:" <> sideName <> ":done")

doneOutcome :: Outcome
doneOutcome = Outcome "Done"

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState
  { rootOpenResources = mempty
  , rootOpenObligations = mempty
  , rootPendingObservables = mempty
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
