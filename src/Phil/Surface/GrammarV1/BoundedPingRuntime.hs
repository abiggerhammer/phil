{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.BoundedPingRuntime
  ( GrammarV1RootCountValue (..)
  , GrammarV1BoundedPingRuntimePlan (..)
  , GrammarV1BoundedPingIteration (..)
  , GrammarV1BoundedPingRuntimeEvidence (..)
  , GrammarV1BoundedPingRuntimeError (..)
  , grammarV1ResolveBoundedPingRuntime
  , grammarV1RunBoundedPingFromSource
  , grammarV1RunBoundedPing
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityExerciseSource
  , AuthorityState
  )
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Process
  ( ProcessKey
  , ProcessNetwork
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey
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
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , ScalarType (..)
  , scalarLiteralInRange
  , scalarLiteralType
  )
import Phil.Core.Syntax
  ( Control (..)
  , Mode (..)
  , Name (..)
  , ObligationId (..)
  , Outcome (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Core.UIntArithmetic
  ( PlainUIntArithmeticDecision (..)
  , PlainUIntArithmeticSite (..)
  , UIntArithmeticError
  , UIntArithmeticOperator (..)
  , checkPlainUIntArithmetic
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
import Phil.Surface.GrammarV1.BoundedPingLoopSource
  ( GrammarV1CheckedBoundedPingLoop (..)
  )
import Phil.Surface.GrammarV1.BoundedPingSourceValues
  ( GrammarV1BoundedPingSourceValues (..)
  )

-- | Concrete runtime input for the exact root entry wired to the bounded
-- client's source-level count parameter.
data GrammarV1RootCountValue = GrammarV1RootCountValue
  { rootCountOccurrence :: ActivationOccurrenceKey
  , rootCountValue :: ScalarLiteral
  }
  deriving (Eq, Show)

-- | Static join between #1145's exact loop-state identities and architecture
-- provisioning.  The loop coordinate has one stable source binder while each
-- runtime protocol transition still receives a fresh endpoint name.
data GrammarV1BoundedPingRuntimePlan = GrammarV1BoundedPingRuntimePlan
  { boundedPingRuntimeLoopSource :: GrammarV1CheckedBoundedPingLoop
  , boundedPingRuntimeCountParameter :: GrammarV1ProvisionedComponentParameter
  , boundedPingRuntimeCountOccurrence :: ActivationOccurrenceKey
  , boundedPingRuntimeClientProcess :: ProcessKey
  , boundedPingRuntimeServerProcess :: ProcessKey
  , boundedPingRuntimeClientEndpoint :: Name
  , boundedPingRuntimeServerEndpoint :: Name
  , boundedPingRuntimeInstance :: ProtocolInstanceRevision
  , boundedPingRuntimeClientRole :: ProtocolRoleKey
  , boundedPingRuntimeServerRole :: ProtocolRoleKey
  }
  deriving (Eq, Show)

-- | One completed Ping branch.  Fresh runtime endpoint names are retained beside
-- the stable source loop-state binders and exact before/after counter values.
data GrammarV1BoundedPingIteration = GrammarV1BoundedPingIteration
  { boundedPingIterationIndex :: Int
  , boundedPingIterationRemainingBefore :: Integer
  , boundedPingIterationRemainingAfter :: Integer
  , boundedPingIterationClientEntryEndpoint :: Name
  , boundedPingIterationServerEntryEndpoint :: Name
  , boundedPingIterationClientBackedgeEndpoint :: Name
  , boundedPingIterationServerBackedgeEndpoint :: Name
  , boundedPingIterationRequestValue :: ScalarLiteral
  , boundedPingIterationReplyText :: Text
  , boundedPingIterationConsoleWrite :: CheckedConsoleWrite
  }
  deriving (Eq, Show)

data GrammarV1BoundedPingRuntimeEvidence = GrammarV1BoundedPingRuntimeEvidence
  { boundedPingEvidenceEndpointStateBinder :: GrammarV1ResolvedBinder
  , boundedPingEvidenceCountStateBinder :: GrammarV1ResolvedBinder
  , boundedPingEvidenceCountOccurrence :: ActivationOccurrenceKey
  , boundedPingEvidenceInitialCount :: Integer
  , boundedPingEvidenceIterations :: [GrammarV1BoundedPingIteration]
  , boundedPingEvidenceTerminalFact :: RootTerminalFact
  }
  deriving (Eq, Show)

data GrammarV1BoundedPingRuntimeError
  = GrammarV1BoundedPingRuntimeParameterMissing GrammarV1BinderKey
  | GrammarV1BoundedPingRuntimeParameterAmbiguous GrammarV1BinderKey
  | GrammarV1BoundedPingRuntimeServerEndpointShape
  | GrammarV1BoundedPingRuntimeCountNotEntry GrammarV1ComponentProvisioningSource
  | GrammarV1BoundedPingRuntimeEndpointNotProtocol GrammarV1ComponentProvisioningSource
  | GrammarV1BoundedPingRuntimeProtocolOccurrenceMismatch Text Text
  | GrammarV1BoundedPingRuntimeProtocolInstanceMismatch
      ProtocolInstanceRevision
      ProtocolInstanceRevision
  | GrammarV1BoundedPingRuntimeRoleMismatch ProtocolRoleKey ProtocolRoleKey
  | GrammarV1BoundedPingRuntimeCountModeMismatch Mode
  | GrammarV1BoundedPingRuntimeCountTypeMismatch Ty
  | GrammarV1BoundedPingRuntimeCountOccurrenceMismatch
      ActivationOccurrenceKey
      ActivationOccurrenceKey
  | GrammarV1BoundedPingRuntimeScalarOutOfRange ScalarLiteral
  | GrammarV1BoundedPingRuntimeScalarTypeMismatch Ty Ty
  | GrammarV1BoundedPingRuntimeCountLiteralRequired ScalarLiteral
  | GrammarV1BoundedPingRuntimeRequestLiteralRequired ScalarLiteral
  | GrammarV1BoundedPingRuntimeProcessError ProcessRendezvousError
  | GrammarV1BoundedPingRuntimeArithmeticError UIntArithmeticError
  | GrammarV1BoundedPingRuntimeArithmeticDidNotEstablish
  | GrammarV1BoundedPingRuntimeConsoleError ConsoleCheckError
  | GrammarV1BoundedPingRuntimeClosureError ProcessEndpointClosureError
  | GrammarV1BoundedPingRuntimeLifecycleError ProcessLifecycleError
  | GrammarV1BoundedPingRuntimeNotTerminal ProcessNetworkDisposition
  deriving (Eq, Show)

-- | Resolve the exact count entry and recursive endpoint occurrence selected by
-- architecture provisioning.  The client parameter identities must be the same
-- declaration-rooted identities established by #1145.
grammarV1ResolveBoundedPingRuntime
  :: GrammarV1CheckedBoundedPingLoop
  -> GrammarV1ResolvedComponentProvisioning
  -> GrammarV1ResolvedComponentProvisioning
  -> Either GrammarV1BoundedPingRuntimeError GrammarV1BoundedPingRuntimePlan
grammarV1ResolveBoundedPingRuntime loopSource clientProvisioning serverProvisioning = do
  clientEndpoint <- requireParameter
    clientProvisioning
    (grammarV1ResolvedBinderKey (boundedPingEndpointParameter loopSource))
  countParameter <- requireParameter
    clientProvisioning
    (grammarV1ResolvedBinderKey (boundedPingCountParameter loopSource))
  serverEndpoint <- requireOnlyServerEndpoint serverProvisioning

  (clientOccurrence, clientProjection) <- endpointSource clientEndpoint
  (serverOccurrence, serverProjection) <- endpointSource serverEndpoint
  if clientOccurrence == serverOccurrence
    then Right ()
    else Left
      (GrammarV1BoundedPingRuntimeProtocolOccurrenceMismatch
        clientOccurrence serverOccurrence)
  if protocolProjectionInstance clientProjection
      == protocolProjectionInstance serverProjection
    then Right ()
    else Left
      (GrammarV1BoundedPingRuntimeProtocolInstanceMismatch
        (protocolProjectionInstance clientProjection)
        (protocolProjectionInstance serverProjection))
  if protocolProjectionRole clientProjection == ProtocolRoleKey "Client"
      && protocolProjectionRole serverProjection == ProtocolRoleKey "Server"
    then Right ()
    else Left
      (GrammarV1BoundedPingRuntimeRoleMismatch
        (protocolProjectionRole clientProjection)
        (protocolProjectionRole serverProjection))

  case provisionedComponentParameterSource countParameter of
    GrammarV1ComponentProvisioningEntry _ _ -> Right ()
    other -> Left (GrammarV1BoundedPingRuntimeCountNotEntry other)
  let countMode = provisionedComponentParameterCheckedMode countParameter
  case checkedBindingMode countMode of
    Unrestricted -> Right ()
    other -> Left (GrammarV1BoundedPingRuntimeCountModeMismatch other)
  if checkedBindingType countMode == TyUInt 32
    then Right ()
    else Left
      (GrammarV1BoundedPingRuntimeCountTypeMismatch
        (checkedBindingType countMode))

  Right GrammarV1BoundedPingRuntimePlan
    { boundedPingRuntimeLoopSource = loopSource
    , boundedPingRuntimeCountParameter = countParameter
    , boundedPingRuntimeCountOccurrence =
        provisionedComponentParameterOccurrence countParameter
    , boundedPingRuntimeClientProcess =
        resolvedProvisioningProcessKey clientProvisioning
    , boundedPingRuntimeServerProcess =
        resolvedProvisioningProcessKey serverProvisioning
    , boundedPingRuntimeClientEndpoint = grammarV1ResolvedBinderCoreName
        (provisionedComponentParameterBinder clientEndpoint)
    , boundedPingRuntimeServerEndpoint = grammarV1ResolvedBinderCoreName
        (provisionedComponentParameterBinder serverEndpoint)
    , boundedPingRuntimeInstance = protocolProjectionInstance clientProjection
    , boundedPingRuntimeClientRole = protocolProjectionRole clientProjection
    , boundedPingRuntimeServerRole = protocolProjectionRole serverProjection
    }
  where
    requireParameter provisioning key =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == key
        ] of
        [] -> Left (GrammarV1BoundedPingRuntimeParameterMissing key)
        [parameter] -> Right parameter
        _ -> Left (GrammarV1BoundedPingRuntimeParameterAmbiguous key)

    requireOnlyServerEndpoint provisioning =
      case
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , case provisionedComponentParameterSource parameter of
            GrammarV1ComponentProvisioningProtocolEndpoint _ _ -> True
            _ -> False
        ] of
        [parameter] -> Right parameter
        _ -> Left GrammarV1BoundedPingRuntimeServerEndpointShape

    endpointSource parameter =
      case provisionedComponentParameterSource parameter of
        GrammarV1ComponentProvisioningProtocolEndpoint occurrence projection ->
          Right (occurrence, projection)
        other -> Left (GrammarV1BoundedPingRuntimeEndpointNotProtocol other)

-- | Execute bounded Ping using only values already extracted from checked
-- positive-round source syntax.  This is the INT-009 Stage-3 composition
-- boundary: request/reply values can no longer be supplied independently of
-- the checked source carrier.
grammarV1RunBoundedPingFromSource
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1BoundedPingRuntimePlan
  -> GrammarV1RootCountValue
  -> GrammarV1BoundedPingSourceValues
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleWriteOutcome
  -> Either
      GrammarV1BoundedPingRuntimeError
      (ProcessCommunicationState, GrammarV1BoundedPingRuntimeEvidence)
grammarV1RunBoundedPingFromSource
    instanceValue network communication plan countInput sourceValues
    authoritySource authorityState writeOutcome =
  grammarV1RunBoundedPing
    instanceValue
    network
    communication
    plan
    countInput
    (boundedPingSourceRequestValue sourceValues)
    (boundedPingSourceReplyText sourceValues)
    authoritySource
    authorityState
    writeOutcome

-- | Execute a bounded recursive Ping run.  A positive remaining count selects
-- Ping, performs one U8 request/String reply rendezvous, writes the exact reply
-- through checked standard.stdout, checks exact U32 subtraction by one, and
-- feeds the fresh successor endpoint plus decremented count through the stable
-- source loop-state coordinates.  Zero selects Done, closes both exact terminal
-- endpoints, and constructs a genuine root terminal fact.
grammarV1RunBoundedPing
  :: BinaryProtocolInstance
  -> ProcessNetwork
  -> ProcessCommunicationState
  -> GrammarV1BoundedPingRuntimePlan
  -> GrammarV1RootCountValue
  -> ScalarLiteral
  -> Text
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleWriteOutcome
  -> Either
      GrammarV1BoundedPingRuntimeError
      (ProcessCommunicationState, GrammarV1BoundedPingRuntimeEvidence)
grammarV1RunBoundedPing
    instanceValue network communication plan countInput requestValue replyText
    authoritySource authorityState writeOutcome = do
  if binaryProtocolInstanceRevision instanceValue == boundedPingRuntimeInstance plan
    then Right ()
    else Left
      (GrammarV1BoundedPingRuntimeProtocolInstanceMismatch
        (boundedPingRuntimeInstance plan)
        (binaryProtocolInstanceRevision instanceValue))
  count <- checkedCount
  checkedRequest
  (closedCommunication, iterations, terminalFact) <- go
    True
    0
    communication
    (boundedPingRuntimeClientEndpoint plan)
    (boundedPingRuntimeServerEndpoint plan)
    count
    []
  Right
    ( closedCommunication
    , GrammarV1BoundedPingRuntimeEvidence
        { boundedPingEvidenceEndpointStateBinder =
            boundedPingEndpointState (boundedPingRuntimeLoopSource plan)
        , boundedPingEvidenceCountStateBinder =
            boundedPingCountState (boundedPingRuntimeLoopSource plan)
        , boundedPingEvidenceCountOccurrence = boundedPingRuntimeCountOccurrence plan
        , boundedPingEvidenceInitialCount = count
        , boundedPingEvidenceIterations = reverse iterations
        , boundedPingEvidenceTerminalFact = terminalFact
        }
    )
  where
    checkedCount = do
      let expectedOccurrence = boundedPingRuntimeCountOccurrence plan
          actualOccurrence = rootCountOccurrence countInput
          literal = rootCountValue countInput
      if actualOccurrence == expectedOccurrence
        then Right ()
        else Left
          (GrammarV1BoundedPingRuntimeCountOccurrenceMismatch
            expectedOccurrence actualOccurrence)
      checkScalar (TyUInt 32) literal
      case literal of
        ScalarUIntLiteral 32 value -> Right value
        other -> Left (GrammarV1BoundedPingRuntimeCountLiteralRequired other)

    checkedRequest = do
      checkScalar (TyUInt 8) requestValue
      case requestValue of
        ScalarUIntLiteral 8 _ -> Right ()
        other -> Left (GrammarV1BoundedPingRuntimeRequestLiteralRequired other)

    checkScalar expected literal = do
      if scalarLiteralInRange literal
        then Right ()
        else Left (GrammarV1BoundedPingRuntimeScalarOutOfRange literal)
      let actual = case scalarLiteralType literal of
            ScalarBool -> TyBool
            ScalarUInt width -> TyUInt width
      if actual == expected
        then Right ()
        else Left (GrammarV1BoundedPingRuntimeScalarTypeMismatch expected actual)

    go firstStep index state clientEndpoint serverEndpoint remaining iterations
      | remaining == 0 = finish firstStep index state clientEndpoint serverEndpoint iterations
      | otherwise = do
          let clientSelected = freshClient index "selected"
              serverSelected = freshServer index "selected"
              clientAwaiting = freshClient index "awaiting"
              serverReply = freshServer index "reply"
              clientBackedge = freshClient index "loop"
              serverBackedge = freshServer index "loop"
              pingChoice = SelectOfferRendezvous
                (side (boundedPingRuntimeClientProcess plan) clientEndpoint clientSelected
                  (boundedPingRuntimeClientRole plan))
                (side (boundedPingRuntimeServerProcess plan) serverEndpoint serverSelected
                  (boundedPingRuntimeServerRole plan))
                "Ping"
              request = SendReceiveRendezvous
                (side (boundedPingRuntimeClientProcess plan) clientSelected clientAwaiting
                  (boundedPingRuntimeClientRole plan))
                (side (boundedPingRuntimeServerProcess plan) serverSelected serverReply
                  (boundedPingRuntimeServerRole plan))
              reply = SendReceiveRendezvous
                (side (boundedPingRuntimeServerProcess plan) serverReply serverBackedge
                  (boundedPingRuntimeServerRole plan))
                (side (boundedPingRuntimeClientProcess plan) clientAwaiting clientBackedge
                  (boundedPingRuntimeClientRole plan))
          afterChoice <- advanceChoice firstStep state pingChoice
          afterRequest <- processSuccessor afterChoice request
          afterReply <- processSuccessor afterRequest reply
          checkedWrite <- mapLeft GrammarV1BoundedPingRuntimeConsoleError $
            checkConsoleWrite
              (consoleEnvironmentStdout standardConsoleEnvironment)
              authoritySource
              authorityState
              replyText
              writeOutcome
          nextRemaining <- decrement index remaining
          let iteration = GrammarV1BoundedPingIteration
                { boundedPingIterationIndex = index
                , boundedPingIterationRemainingBefore = remaining
                , boundedPingIterationRemainingAfter = nextRemaining
                , boundedPingIterationClientEntryEndpoint = clientEndpoint
                , boundedPingIterationServerEntryEndpoint = serverEndpoint
                , boundedPingIterationClientBackedgeEndpoint = clientBackedge
                , boundedPingIterationServerBackedgeEndpoint = serverBackedge
                , boundedPingIterationRequestValue = requestValue
                , boundedPingIterationReplyText = replyText
                , boundedPingIterationConsoleWrite = checkedWrite
                }
          go False (index + 1) afterReply clientBackedge serverBackedge
            nextRemaining (iteration : iterations)

    finish firstStep index state clientEndpoint serverEndpoint iterations = do
      let clientTerminal = freshClient index "done"
          serverTerminal = freshServer index "done"
          doneChoice = SelectOfferRendezvous
            (side (boundedPingRuntimeClientProcess plan) clientEndpoint clientTerminal
              (boundedPingRuntimeClientRole plan))
            (side (boundedPingRuntimeServerProcess plan) serverEndpoint serverTerminal
              (boundedPingRuntimeServerRole plan))
            "Done"
      afterDone <- advanceChoice firstStep state doneChoice
      closedClient <- mapLeft GrammarV1BoundedPingRuntimeClosureError $
        closeProcessEndpointState
          network
          afterDone
          (boundedPingRuntimeClientProcess plan)
          clientTerminal
          (boundedPingRuntimeInstance plan)
          (boundedPingRuntimeClientRole plan)
          doneOutcome
      closedBoth <- mapLeft GrammarV1BoundedPingRuntimeClosureError $
        closeProcessEndpointState
          network
          closedClient
          (boundedPingRuntimeServerProcess plan)
          serverTerminal
          (boundedPingRuntimeInstance plan)
          (boundedPingRuntimeServerRole plan)
          doneOutcome
      runtime0 <- mapLeft GrammarV1BoundedPingRuntimeLifecycleError $
        initializeProcessRuntime network (communicationProtocolContexts closedBoth)
      runtime1 <- mapLeft GrammarV1BoundedPingRuntimeLifecycleError $
        applyDeclaredTerminalTransition
          (terminalTransition (boundedPingRuntimeClientProcess plan)) runtime0
      runtime2 <- mapLeft GrammarV1BoundedPingRuntimeLifecycleError $
        applyDeclaredTerminalTransition
          (terminalTransition (boundedPingRuntimeServerProcess plan)) runtime1
      disposition <- mapLeft GrammarV1BoundedPingRuntimeLifecycleError $
        classifyProcessNetwork emptyRootClosure [] runtime2
      terminalFact <- case disposition of
        NetworkTerminal fact -> Right fact
        other -> Left (GrammarV1BoundedPingRuntimeNotTerminal other)
      Right (closedBoth, iterations, terminalFact)

    advanceChoice firstStep state request
      | firstStep = mapLeft GrammarV1BoundedPingRuntimeProcessError $
          checkProcessCommunicationState instanceValue network state request
      | otherwise = processSuccessor state request

    processSuccessor state request =
      mapLeft GrammarV1BoundedPingRuntimeProcessError $
        checkProcessCommunicationSuccessor instanceValue network state request

    decrement index remaining = do
      let result = remaining - 1
          site = PlainUIntArithmeticSite
            { plainUIntArithmeticObligationId =
                ObligationId ("int009.bounded-ping.decrement." <> Text.pack (show index))
            , plainUIntArithmeticOrigin = "INT-009 bounded Ping runtime"
            , plainUIntArithmeticScope = "ClientCounter.loop.remaining"
            , plainUIntArithmeticRequiredPoint = "loop backedge"
            }
      decision <- mapLeft GrammarV1BoundedPingRuntimeArithmeticError $
        checkPlainUIntArithmetic
          emptyCheckState
          UIntSubtract
          32
          (RefUInt 32 remaining)
          (RefUInt 32 1)
          (RefUInt 32 result)
          site
      case decision of
        PlainUIntArithmeticEstablished (ScalarUIntLiteral 32 established) ->
          Right established
        _ -> Left GrammarV1BoundedPingRuntimeArithmeticDidNotEstablish

    side process endpoint successor role = ProcessRendezvousSide
      { rendezvousProcess = process
      , rendezvousEndpoint = endpoint
      , rendezvousSuccessor = successor
      , rendezvousInstance = boundedPingRuntimeInstance plan
      , rendezvousRole = role
      }

    freshClient index suffix = freshName
      (grammarV1ResolvedBinderCoreName
        (boundedPingEndpointState (boundedPingRuntimeLoopSource plan)))
      "client"
      index
      suffix

    freshServer index suffix = freshName
      (boundedPingRuntimeServerEndpoint plan)
      "server"
      index
      suffix

freshName :: Name -> Text -> Int -> Text -> Name
freshName (Name prefix) sideName index suffix = Name
  (prefix
    <> ":int009:"
    <> sideName
    <> ":"
    <> Text.pack (show index)
    <> ":"
    <> suffix)

doneOutcome :: Outcome
doneOutcome = Outcome "Done"

terminalTransition :: ProcessKey -> DeclaredTerminalTransition
terminalTransition processKey = DeclaredTerminalTransition
  { declaredTerminalProcess = processKey
  , declaredTerminalControl = Closed doneOutcome
  , declaredTerminalDisposals = []
  }

emptyRootClosure :: RootClosureState
emptyRootClosure = RootClosureState Set.empty Set.empty Set.empty

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
