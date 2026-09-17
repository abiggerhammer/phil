{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ComponentRequestReplyRuntime
  ( GrammarV1ResolvedRequestReply (..)
  , GrammarV1RequestReplyRuntimeEvidence (..)
  , GrammarV1RequestReplyRuntimeError (..)
  , grammarV1ResolveRequestReply
  , grammarV1RunRequestReply
  ) where

import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityExerciseSource
  , AuthorityState
  )
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Process
  ( ProcessNetwork
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
  )
import Phil.Core.ProcessRendezvous
  ( ProcessCommunicationState
  , ProcessRendezvousError
  , ProcessRendezvousRequest (..)
  , ProcessRendezvousSide (..)
  , checkProcessCommunicationState
  , checkProcessCommunicationSuccessor
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  , ProtocolProjectionEvidence (..)
  )
import Phil.Core.Scalar
  ( ScalarLiteral
  , ScalarType (..)
  , scalarLiteralInRange
  , scalarLiteralType
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name
  , Session (..)
  , Ty (..)
  )
import Phil.Core.UnicodeString
  ( unicodeStringCoreType
  )
import Phil.IO.Console
  ( CheckedConsoleWrite
  , ConsoleCheckError
  , ConsoleEnvironment (..)
  , ConsoleWriteOutcome
  , checkConsoleWrite
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
import Phil.Surface.GrammarV1.ComponentRequestReplyOutput
  ( GrammarV1CheckedRequestReplyClient (..)
  , GrammarV1CheckedRequestReplyServer (..)
  )

-- | Exact Stage-2 runtime carrier derived from source binders plus architecture
-- provisioning. Both rendezvous requests are fixed before execution: the second
-- one starts at the source-derived successor names produced by the first.
data GrammarV1ResolvedRequestReply = GrammarV1ResolvedRequestReply
  { resolvedRequestReplyClientPayloadParameter :: GrammarV1ProvisionedComponentParameter
  , resolvedRequestReplyRequestOccurrence :: ActivationOccurrenceKey
  , resolvedRequestReplyRequestReceiverBinder :: GrammarV1ResolvedBinder
  , resolvedRequestReplyReplyReceiverBinder :: GrammarV1ResolvedBinder
  , resolvedRequestReplyWriteDecisionBinder :: GrammarV1ResolvedBinder
  , resolvedRequestReplyInitialRequest :: ProcessRendezvousRequest
  , resolvedRequestReplyReplyRequest :: ProcessRendezvousRequest
  , resolvedRequestReplyClientTerminalEndpoint :: Name
  , resolvedRequestReplyServerTerminalEndpoint :: Name
  , resolvedRequestReplyReplyText :: Text
  }
  deriving (Eq, Show)

-- | Evidence for one complete bounded request/reply execution. The same reply
-- text that participates in the successful server->client rendezvous is passed
-- to the exact checked standard.stdout write operation.
data GrammarV1RequestReplyRuntimeEvidence = GrammarV1RequestReplyRuntimeEvidence
  { requestReplyEvidenceRequestOccurrence :: ActivationOccurrenceKey
  , requestReplyEvidenceRequestSenderBinder :: GrammarV1ResolvedBinder
  , requestReplyEvidenceRequestReceiverBinder :: GrammarV1ResolvedBinder
  , requestReplyEvidenceRequestValue :: ScalarLiteral
  , requestReplyEvidenceReplySenderText :: Text
  , requestReplyEvidenceReplyReceiverBinder :: GrammarV1ResolvedBinder
  , requestReplyEvidenceConsoleWrite :: CheckedConsoleWrite
  }
  deriving (Eq, Show)

data GrammarV1RequestReplyRuntimeError
  = GrammarV1RequestReplyParameterMissing GrammarV1BinderKey
  | GrammarV1RequestReplyParameterAmbiguous GrammarV1BinderKey
  | GrammarV1RequestReplyPayloadNotEntry GrammarV1ComponentProvisioningSource
  | GrammarV1RequestReplyEndpointNotProtocol GrammarV1ComponentProvisioningSource
  | GrammarV1RequestReplyProtocolOccurrenceMismatch Text Text
  | GrammarV1RequestReplyProtocolInstanceMismatch
  | GrammarV1RequestReplyClientSessionMismatch Session
  | GrammarV1RequestReplyServerSessionMismatch Session
  | GrammarV1RequestReplyRequestTypeMismatch Ty Ty
  | GrammarV1RequestReplyReplyTypeMismatch Ty Ty
  | GrammarV1RequestReplyRequestModeMismatch Mode
  | GrammarV1RequestReplyEntryOccurrenceMismatch
      ActivationOccurrenceKey
      ActivationOccurrenceKey
  | GrammarV1RequestReplyScalarOutOfRange ScalarLiteral
  | GrammarV1RequestReplyScalarTypeMismatch Ty Ty
  | GrammarV1RequestReplyProcessError ProcessRendezvousError
  | GrammarV1RequestReplyConsoleError ConsoleCheckError
  deriving (Eq, Show)

-- | Join the Stage-2 source carriers to the exact component occurrences selected
-- by architecture provisioning. Display names never participate in the join.
grammarV1ResolveRequestReply
  :: GrammarV1CheckedRequestReplyClient
  -> GrammarV1ResolvedComponentProvisioning
  -> GrammarV1CheckedRequestReplyServer
  -> GrammarV1ResolvedComponentProvisioning
  -> Either GrammarV1RequestReplyRuntimeError GrammarV1ResolvedRequestReply
grammarV1ResolveRequestReply clientPlan clientProvisioning serverPlan serverProvisioning = do
  clientPayload <- requireParameter
    clientProvisioning
    (grammarV1ResolvedBinderKey (requestReplyClientPayload clientPlan))
  clientEndpoint <- requireParameter
    clientProvisioning
    (grammarV1ResolvedBinderKey (requestReplyClientInitialEndpoint clientPlan))
  serverEndpoint <- requireParameter
    serverProvisioning
    (grammarV1ResolvedBinderKey (requestReplyServerInitialEndpoint serverPlan))

  case provisionedComponentParameterSource clientPayload of
    GrammarV1ComponentProvisioningEntry _ _ -> Right ()
    other -> Left (GrammarV1RequestReplyPayloadNotEntry other)

  (clientOccurrence, clientProjection) <- endpointSource clientEndpoint
  (serverOccurrence, serverProjection) <- endpointSource serverEndpoint
  if clientOccurrence == serverOccurrence
    then Right ()
    else Left
      (GrammarV1RequestReplyProtocolOccurrenceMismatch clientOccurrence serverOccurrence)
  if protocolProjectionInstance clientProjection == protocolProjectionInstance serverProjection
    then Right ()
    else Left GrammarV1RequestReplyProtocolInstanceMismatch

  (requestType, clientAfterRequest) <- case protocolProjectionSession clientProjection of
    Send _ ty continuation -> Right (ty, continuation)
    other -> Left (GrammarV1RequestReplyClientSessionMismatch other)
  (serverRequestType, serverAfterRequest) <- case protocolProjectionSession serverProjection of
    Receive _ ty continuation -> Right (ty, continuation)
    other -> Left (GrammarV1RequestReplyServerSessionMismatch other)
  if requestType == serverRequestType
    then Right ()
    else Left (GrammarV1RequestReplyRequestTypeMismatch requestType serverRequestType)
  let payloadType = checkedBindingType
        (provisionedComponentParameterCheckedMode clientPayload)
  if payloadType == requestType
    then Right ()
    else Left (GrammarV1RequestReplyRequestTypeMismatch requestType payloadType)

  replyType <- case clientAfterRequest of
    Receive _ ty _ -> Right ty
    other -> Left (GrammarV1RequestReplyClientSessionMismatch other)
  serverReplyType <- case serverAfterRequest of
    Send _ ty _ -> Right ty
    other -> Left (GrammarV1RequestReplyServerSessionMismatch other)
  if replyType == serverReplyType
    then Right ()
    else Left (GrammarV1RequestReplyReplyTypeMismatch replyType serverReplyType)
  if replyType == unicodeStringCoreType
    then Right ()
    else Left (GrammarV1RequestReplyReplyTypeMismatch unicodeStringCoreType replyType)

  let clientProcess = resolvedProvisioningProcessKey clientProvisioning
      serverProcess = resolvedProvisioningProcessKey serverProvisioning
      clientRole = protocolProjectionRole clientProjection
      serverRole = protocolProjectionRole serverProjection
      instanceRevision = protocolProjectionInstance clientProjection
      clientInitialName = grammarV1ResolvedBinderCoreName
        (provisionedComponentParameterBinder clientEndpoint)
      serverInitialName = grammarV1ResolvedBinderCoreName
        (provisionedComponentParameterBinder serverEndpoint)
      clientReplyName = grammarV1ResolvedBinderCoreName
        (requestReplyClientReplyEndpoint clientPlan)
      serverReplyName = grammarV1ResolvedBinderCoreName
        (requestReplyServerReplyEndpoint serverPlan)
      clientTerminalName = grammarV1ResolvedBinderCoreName
        (requestReplyClientTerminalEndpoint clientPlan)
      serverTerminalName = grammarV1ResolvedBinderCoreName
        (requestReplyServerTerminalEndpoint serverPlan)
      request = SendReceiveRendezvous
        ProcessRendezvousSide
          { rendezvousProcess = clientProcess
          , rendezvousEndpoint = clientInitialName
          , rendezvousSuccessor = clientReplyName
          , rendezvousInstance = instanceRevision
          , rendezvousRole = clientRole
          }
        ProcessRendezvousSide
          { rendezvousProcess = serverProcess
          , rendezvousEndpoint = serverInitialName
          , rendezvousSuccessor = serverReplyName
          , rendezvousInstance = instanceRevision
          , rendezvousRole = serverRole
          }
      reply = SendReceiveRendezvous
        ProcessRendezvousSide
          { rendezvousProcess = serverProcess
          , rendezvousEndpoint = serverReplyName
          , rendezvousSuccessor = serverTerminalName
          , rendezvousInstance = instanceRevision
          , rendezvousRole = serverRole
          }
        ProcessRendezvousSide
          { rendezvousProcess = clientProcess
          , rendezvousEndpoint = clientReplyName
          , rendezvousSuccessor = clientTerminalName
          , rendezvousInstance = instanceRevision
          , rendezvousRole = clientRole
          }
  Right GrammarV1ResolvedRequestReply
    { resolvedRequestReplyClientPayloadParameter = clientPayload
    , resolvedRequestReplyRequestOccurrence =
        provisionedComponentParameterOccurrence clientPayload
    , resolvedRequestReplyRequestReceiverBinder = requestReplyServerRequestValue serverPlan
    , resolvedRequestReplyReplyReceiverBinder = requestReplyClientReplyValue clientPlan
    , resolvedRequestReplyWriteDecisionBinder = requestReplyClientWriteDecision clientPlan
    , resolvedRequestReplyInitialRequest = request
    , resolvedRequestReplyReplyRequest = reply
    , resolvedRequestReplyClientTerminalEndpoint = clientTerminalName
    , resolvedRequestReplyServerTerminalEndpoint = serverTerminalName
    , resolvedRequestReplyReplyText = requestReplyServerReplyText serverPlan
    }
  where
    requireParameter provisioning key =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == key
        ] of
        [] -> Left (GrammarV1RequestReplyParameterMissing key)
        [parameter] -> Right parameter
        _ -> Left (GrammarV1RequestReplyParameterAmbiguous key)

    endpointSource parameter = case provisionedComponentParameterSource parameter of
      GrammarV1ComponentProvisioningProtocolEndpoint occurrence projection ->
        Right (occurrence, projection)
      other -> Left (GrammarV1RequestReplyEndpointNotProtocol other)

-- | Execute both source-derived rendezvous transitions, carry the exact root U8
-- request to the server receive binder, carry the server's exact String reply to
-- the client reply binder, and write that same reply through standard.stdout.
grammarV1RunRequestReply
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1ResolvedRequestReply
  -> ActivationOccurrenceKey
  -> ScalarLiteral
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleWriteOutcome
  -> Either
      GrammarV1RequestReplyRuntimeError
      (ProcessCommunicationState, GrammarV1RequestReplyRuntimeEvidence)
grammarV1RunRequestReply
    instanceValue network communication resolved actualOccurrence requestValue
    authoritySource authorityState writeOutcome = do
  let payloadParameter = resolvedRequestReplyClientPayloadParameter resolved
      checkedMode = provisionedComponentParameterCheckedMode payloadParameter
      expectedOccurrence = resolvedRequestReplyRequestOccurrence resolved
      expectedType = checkedBindingType checkedMode
      actualType = scalarLiteralCoreType requestValue
  case checkedBindingMode checkedMode of
    Unrestricted -> Right ()
    other -> Left (GrammarV1RequestReplyRequestModeMismatch other)
  if actualOccurrence == expectedOccurrence
    then Right ()
    else Left
      (GrammarV1RequestReplyEntryOccurrenceMismatch expectedOccurrence actualOccurrence)
  if scalarLiteralInRange requestValue
    then Right ()
    else Left (GrammarV1RequestReplyScalarOutOfRange requestValue)
  if actualType == expectedType
    then Right ()
    else Left (GrammarV1RequestReplyScalarTypeMismatch expectedType actualType)

  afterRequest <- mapLeft GrammarV1RequestReplyProcessError $
    checkProcessCommunicationState
      instanceValue network communication (resolvedRequestReplyInitialRequest resolved)
  afterReply <- mapLeft GrammarV1RequestReplyProcessError $
    checkProcessCommunicationSuccessor
      instanceValue network afterRequest (resolvedRequestReplyReplyRequest resolved)

  let stdout = consoleEnvironmentStdout standardConsoleEnvironment
      replyText = resolvedRequestReplyReplyText resolved
  checkedWrite <- mapLeft GrammarV1RequestReplyConsoleError $
    checkConsoleWrite stdout authoritySource authorityState replyText writeOutcome

  Right
    ( afterReply
    , GrammarV1RequestReplyRuntimeEvidence
        { requestReplyEvidenceRequestOccurrence = expectedOccurrence
        , requestReplyEvidenceRequestSenderBinder =
            provisionedComponentParameterBinder payloadParameter
        , requestReplyEvidenceRequestReceiverBinder =
            resolvedRequestReplyRequestReceiverBinder resolved
        , requestReplyEvidenceRequestValue = requestValue
        , requestReplyEvidenceReplySenderText = replyText
        , requestReplyEvidenceReplyReceiverBinder =
            resolvedRequestReplyReplyReceiverBinder resolved
        , requestReplyEvidenceConsoleWrite = checkedWrite
        }
    )

scalarLiteralCoreType :: ScalarLiteral -> Ty
scalarLiteralCoreType literal =
  case scalarLiteralType literal of
    ScalarBool -> TyBool
    ScalarUInt width -> TyUInt width

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
