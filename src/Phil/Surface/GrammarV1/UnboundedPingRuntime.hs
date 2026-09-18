{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.UnboundedPingRuntime
  ( GrammarV1UnboundedPingRuntimePlan (..)
  , GrammarV1UnboundedPingIteration (..)
  , GrammarV1UnboundedPingRuntimeEvidence (..)
  , GrammarV1UnboundedPingRuntimeError (..)
  , grammarV1ResolveUnboundedPingRuntime
  , grammarV1RunUnboundedPingPrefix
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityExerciseSource
  , AuthorityState
  )
import Phil.Core.Process
  ( ProcessKey
  , ProcessNetwork
  )
import Phil.Core.ProcessLifecycle
  ( EnabledProcessTransition (..)
  , ProcessLifecycleError
  , ProcessNetworkDisposition (..)
  , RootClosureState (..)
  , classifyProcessNetwork
  , initializeProcessRuntime
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState (..)
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , checkProcessCommunicationState
  , checkProcessCommunicationSuccessor
  )
import Phil.Core.Protocol
  ( ProtocolInstanceRevision
  , ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance (..)
  , ProtocolProjectionEvidence (..)
  )
import Phil.Core.Scalar (ScalarLiteral)
import Phil.Core.Syntax (Name (..))
import Phil.IO.Console
  ( CheckedConsoleWrite
  , ConsoleCheckError
  , ConsoleWriteOutcome
  , checkConsoleWrite
  , consoleEnvironmentStdout
  , standardConsoleEnvironment
  )
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.UnboundedPingSource
  ( GrammarV1CheckedUnboundedPingSource (..)
  )

data GrammarV1UnboundedPingRuntimePlan = GrammarV1UnboundedPingRuntimePlan
  { unboundedPingRuntimeSource :: GrammarV1CheckedUnboundedPingSource
  , unboundedPingRuntimeClientProcess :: ProcessKey
  , unboundedPingRuntimeServerProcess :: ProcessKey
  , unboundedPingRuntimeClientEndpoint :: Name
  , unboundedPingRuntimeServerEndpoint :: Name
  , unboundedPingRuntimeInstance :: ProtocolInstanceRevision
  , unboundedPingRuntimeClientRole :: ProtocolRoleKey
  , unboundedPingRuntimeServerRole :: ProtocolRoleKey
  }
  deriving (Eq, Show)

data GrammarV1UnboundedPingIteration = GrammarV1UnboundedPingIteration
  { unboundedPingIterationIndex :: Int
  , unboundedPingIterationClientEntryEndpoint :: Name
  , unboundedPingIterationServerEntryEndpoint :: Name
  , unboundedPingIterationClientBackedgeEndpoint :: Name
  , unboundedPingIterationServerBackedgeEndpoint :: Name
  , unboundedPingIterationRequestValue :: ScalarLiteral
  , unboundedPingIterationReplyText :: Text
  , unboundedPingIterationConsoleWrite :: CheckedConsoleWrite
  }
  deriving (Eq, Show)

data GrammarV1UnboundedPingRuntimeEvidence = GrammarV1UnboundedPingRuntimeEvidence
  { unboundedPingEvidenceIterations :: [GrammarV1UnboundedPingIteration]
  , unboundedPingEvidenceFinalClientEndpoint :: Name
  , unboundedPingEvidenceFinalServerEndpoint :: Name
  , unboundedPingEvidenceDisposition :: ProcessNetworkDisposition
  }
  deriving (Eq, Show)

data GrammarV1UnboundedPingRuntimeError
  = GrammarV1UnboundedPingRuntimeParameterMissing GrammarV1BinderKey
  | GrammarV1UnboundedPingRuntimeParameterAmbiguous GrammarV1BinderKey
  | GrammarV1UnboundedPingRuntimeEndpointNotProtocol GrammarV1ComponentProvisioningSource
  | GrammarV1UnboundedPingRuntimeProtocolOccurrenceMismatch Text Text
  | GrammarV1UnboundedPingRuntimeProtocolInstanceMismatch
      ProtocolInstanceRevision
      ProtocolInstanceRevision
  | GrammarV1UnboundedPingRuntimeRoleMismatch ProtocolRoleKey ProtocolRoleKey
  | GrammarV1UnboundedPingRuntimePrefixMustBePositive Int
  | GrammarV1UnboundedPingRuntimeProcessError ProcessRendezvousError
  | GrammarV1UnboundedPingRuntimeConsoleError ConsoleCheckError
  | GrammarV1UnboundedPingRuntimeLifecycleError ProcessLifecycleError
  | GrammarV1UnboundedPingRuntimeUnexpectedDisposition ProcessNetworkDisposition
  deriving (Eq, Show)

grammarV1ResolveUnboundedPingRuntime
  :: GrammarV1CheckedUnboundedPingSource
  -> GrammarV1ResolvedComponentProvisioning
  -> GrammarV1ResolvedComponentProvisioning
  -> Either GrammarV1UnboundedPingRuntimeError GrammarV1UnboundedPingRuntimePlan
grammarV1ResolveUnboundedPingRuntime source clientProvisioning serverProvisioning = do
  clientEndpoint <- requireParameter
    clientProvisioning
    (grammarV1ResolvedBinderKey (unboundedPingClientEndpointParameter source))
  serverEndpoint <- requireParameter
    serverProvisioning
    (grammarV1ResolvedBinderKey (unboundedPingServerEndpointParameter source))
  (clientOccurrence, clientProjection) <- endpointSource clientEndpoint
  (serverOccurrence, serverProjection) <- endpointSource serverEndpoint
  if clientOccurrence == serverOccurrence
    then Right ()
    else Left
      (GrammarV1UnboundedPingRuntimeProtocolOccurrenceMismatch
        clientOccurrence serverOccurrence)
  if protocolProjectionInstance clientProjection
      == protocolProjectionInstance serverProjection
    then Right ()
    else Left
      (GrammarV1UnboundedPingRuntimeProtocolInstanceMismatch
        (protocolProjectionInstance clientProjection)
        (protocolProjectionInstance serverProjection))
  if protocolProjectionRole clientProjection == ProtocolRoleKey "Client"
      && protocolProjectionRole serverProjection == ProtocolRoleKey "Server"
    then Right ()
    else Left
      (GrammarV1UnboundedPingRuntimeRoleMismatch
        (protocolProjectionRole clientProjection)
        (protocolProjectionRole serverProjection))
  Right GrammarV1UnboundedPingRuntimePlan
    { unboundedPingRuntimeSource = source
    , unboundedPingRuntimeClientProcess =
        resolvedProvisioningProcessKey clientProvisioning
    , unboundedPingRuntimeServerProcess =
        resolvedProvisioningProcessKey serverProvisioning
    , unboundedPingRuntimeClientEndpoint =
        grammarV1ResolvedBinderCoreName
          (provisionedComponentParameterBinder clientEndpoint)
    , unboundedPingRuntimeServerEndpoint =
        grammarV1ResolvedBinderCoreName
          (provisionedComponentParameterBinder serverEndpoint)
    , unboundedPingRuntimeInstance = protocolProjectionInstance clientProjection
    , unboundedPingRuntimeClientRole = protocolProjectionRole clientProjection
    , unboundedPingRuntimeServerRole = protocolProjectionRole serverProjection
    }
  where
    requireParameter provisioning key =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == key
        ] of
        [] -> Left (GrammarV1UnboundedPingRuntimeParameterMissing key)
        [parameter] -> Right parameter
        _ -> Left (GrammarV1UnboundedPingRuntimeParameterAmbiguous key)

    endpointSource parameter =
      case provisionedComponentParameterSource parameter of
        GrammarV1ComponentProvisioningProtocolEndpoint occurrence projection ->
          Right (occurrence, projection)
        other -> Left (GrammarV1UnboundedPingRuntimeEndpointNotProtocol other)

grammarV1RunUnboundedPingPrefix
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1UnboundedPingRuntimePlan
  -> Int
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleWriteOutcome
  -> Either
      GrammarV1UnboundedPingRuntimeError
      (ProcessCommunicationState, GrammarV1UnboundedPingRuntimeEvidence)
grammarV1RunUnboundedPingPrefix
    instanceValue network communication plan prefixRounds
    authoritySource authorityState writeOutcome = do
  if prefixRounds > 0
    then Right ()
    else Left (GrammarV1UnboundedPingRuntimePrefixMustBePositive prefixRounds)
  if binaryProtocolInstanceRevision instanceValue == unboundedPingRuntimeInstance plan
    then Right ()
    else Left
      (GrammarV1UnboundedPingRuntimeProtocolInstanceMismatch
        (unboundedPingRuntimeInstance plan)
        (binaryProtocolInstanceRevision instanceValue))
  (afterPrefix, clientEndpoint, serverEndpoint, iterations) <-
    go True 0 prefixRounds communication
      (unboundedPingRuntimeClientEndpoint plan)
      (unboundedPingRuntimeServerEndpoint plan)
      []
  runtime <- mapLeft GrammarV1UnboundedPingRuntimeLifecycleError $
    initializeProcessRuntime network (communicationProtocolContexts afterPrefix)
  disposition <- mapLeft GrammarV1UnboundedPingRuntimeLifecycleError $
    classifyProcessNetwork
      emptyRootClosure
      [ EnabledRendezvousStep
          (unboundedPingRuntimeClientProcess plan)
          (unboundedPingRuntimeServerProcess plan)
      ]
      runtime
  case disposition of
    NetworkCanStep -> Right
      ( afterPrefix
      , GrammarV1UnboundedPingRuntimeEvidence
          { unboundedPingEvidenceIterations = reverse iterations
          , unboundedPingEvidenceFinalClientEndpoint = clientEndpoint
          , unboundedPingEvidenceFinalServerEndpoint = serverEndpoint
          , unboundedPingEvidenceDisposition = disposition
          }
      )
    other -> Left (GrammarV1UnboundedPingRuntimeUnexpectedDisposition other)
  where
    source = unboundedPingRuntimeSource plan
    requestValue = unboundedPingSourceRequestValue source
    replyText = unboundedPingSourceReplyText source

    go firstStep index remaining state clientEndpoint serverEndpoint iterations
      | remaining == 0 =
          Right (state, clientEndpoint, serverEndpoint, iterations)
      | otherwise = do
          let clientSelected = freshClient index "selected"
              serverSelected = freshServer index "selected"
              clientAwaiting = freshClient index "awaiting"
              serverReply = freshServer index "reply"
              clientBackedge = freshClient index "loop"
              serverBackedge = freshServer index "loop"
              pingChoice = SelectOfferRendezvous
                (side
                  (unboundedPingRuntimeClientProcess plan)
                  clientEndpoint
                  clientSelected
                  (unboundedPingRuntimeClientRole plan))
                (side
                  (unboundedPingRuntimeServerProcess plan)
                  serverEndpoint
                  serverSelected
                  (unboundedPingRuntimeServerRole plan))
                "Ping"
              request = SendReceiveRendezvous
                (side
                  (unboundedPingRuntimeClientProcess plan)
                  clientSelected
                  clientAwaiting
                  (unboundedPingRuntimeClientRole plan))
                (side
                  (unboundedPingRuntimeServerProcess plan)
                  serverSelected
                  serverReply
                  (unboundedPingRuntimeServerRole plan))
              reply = SendReceiveRendezvous
                (side
                  (unboundedPingRuntimeServerProcess plan)
                  serverReply
                  serverBackedge
                  (unboundedPingRuntimeServerRole plan))
                (side
                  (unboundedPingRuntimeClientProcess plan)
                  clientAwaiting
                  clientBackedge
                  (unboundedPingRuntimeClientRole plan))
          afterChoice <- advanceChoice firstStep state pingChoice
          afterRequest <- processSuccessor afterChoice request
          afterReply <- processSuccessor afterRequest reply
          checkedWrite <- mapLeft GrammarV1UnboundedPingRuntimeConsoleError $
            checkConsoleWrite
              (consoleEnvironmentStdout standardConsoleEnvironment)
              authoritySource
              authorityState
              replyText
              writeOutcome
          let iteration = GrammarV1UnboundedPingIteration
                { unboundedPingIterationIndex = index
                , unboundedPingIterationClientEntryEndpoint = clientEndpoint
                , unboundedPingIterationServerEntryEndpoint = serverEndpoint
                , unboundedPingIterationClientBackedgeEndpoint = clientBackedge
                , unboundedPingIterationServerBackedgeEndpoint = serverBackedge
                , unboundedPingIterationRequestValue = requestValue
                , unboundedPingIterationReplyText = replyText
                , unboundedPingIterationConsoleWrite = checkedWrite
                }
          go False (index + 1) (remaining - 1) afterReply
            clientBackedge serverBackedge (iteration : iterations)

    advanceChoice firstStep state request
      | firstStep = mapLeft GrammarV1UnboundedPingRuntimeProcessError $
          checkProcessCommunicationState instanceValue network state request
      | otherwise = processSuccessor state request

    processSuccessor state request =
      mapLeft GrammarV1UnboundedPingRuntimeProcessError $
        checkProcessCommunicationSuccessor instanceValue network state request

    side process endpoint successor role = ProcessRendezvousSide
      { rendezvousProcess = process
      , rendezvousEndpoint = endpoint
      , rendezvousSuccessor = successor
      , rendezvousInstance = unboundedPingRuntimeInstance plan
      , rendezvousRole = role
      }

    freshClient index suffix =
      freshName
        (grammarV1ResolvedBinderCoreName
          (unboundedPingClientEndpointState source))
        "client"
        index
        suffix

    freshServer index suffix =
      freshName
        (grammarV1ResolvedBinderCoreName
          (unboundedPingServerEndpointState source))
        "server"
        index
        suffix

freshName :: Name -> Text -> Int -> Text -> Name
freshName (Name prefix) sideName index suffix = Name
  ( prefix
    <> ":int009:unbounded:"
    <> sideName
    <> ":"
    <> Text.pack (show index)
    <> ":"
    <> suffix
  )

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState
  { rootOpenResources = mempty
  , rootOpenObligations = mempty
  , rootPendingObservables = mempty
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
