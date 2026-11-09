{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Context (CheckError (..), ResourceContext (..), insertBinding)
import Phil.Core.Generic (GenericStaticParameterKey (..), strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessRendezvous
import Phil.Core.ProcessEndpointClosure (ProcessEndpointClosureError (..))
import Phil.Core.ProcessLifecycle
import Phil.Core.Session (SessionError (..))
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentReceiveClose
import Phil.Surface.GrammarV1.ComponentRestrictedRendezvous
import Phil.Surface.GrammarV1.ComponentRestrictedSourceTerminal
import Phil.Surface.GrammarV1.ComponentRestrictedSourceClose
import Phil.Surface.GrammarV1.ComponentSendClose
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1CheckedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  accepted <- TextIO.readFile
    "test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil"
  rejected <- TextIO.readFile
    "test/fixtures/fsem02-restricted-source-transfer-v1/rejected-stale-close.phil"
  let result = do
        fx <- fixture accepted
        sequence_
          [ acceptedReplay fx
          , staleOwnerRejects fx
          , missingOwnerRejects fx
          , duplicateReceiverRejects fx
          , wrongSourceCloseRejects fx rejected
          , wrongSourcePayloadModeRejects fx accepted
          , wrongWrittenReceiveTypeRejects fx accepted
          , wrongProtocolBinderRejects accepted
          , wrongSessionHeadRejects fx
          , sourceCloseReplay fx
          , sourceCloseRejectsForgedRequest fx
          , sourceCloseRejectsForgedPayloadBinder fx
          , sourceCloseRejectsForgedReceiveBinder fx
          , sourceCloseRejectedSpelling fx rejected
          , sourceCloseMissingServerOwner fx
          , sourceCloseWrongOutcome fx
          , sourceCloseWrongHead fx
          , sourceCloseWrongRole fx
          , sourceTerminalReplay fx
          , sourceTerminalNegativeGates fx
          , sourceTerminalRejectForgedClosedState fx
          , sourceTerminalRejectStaleSenderReplay fx
          , sourceTerminalRejectStaleReceiverReplay fx
          ]
  case result of
    Right () -> putStrLn "PASS: FSEM-02 source restricted transfer and exact negative replay"
    Left err -> putStrLn ("FAIL: " <> err) >> exitFailure

data Fixture = Fixture
  { fxSender :: GrammarV1ComponentDecl
  , fxReceiver :: GrammarV1ComponentDecl
  , fxInstance :: BinaryProtocolInstance
  , fxNetwork :: ProcessNetwork
  , fxBefore :: ProcessCommunicationState
  , fxClientProcess :: ProcessKey
  , fxServerProcess :: ProcessKey
  , fxClientOld :: Name
  , fxServerOld :: Name
  , fxClientNext :: Name
  , fxServerNext :: Name
  , fxPayloadOwner :: Name
  , fxPayloadReceiver :: Name
  }

parseParts :: Text -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl, GrammarV1ComponentDecl)
parseParts source = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "fsem02-restricted-source-v1" source
  let declarations = map (locatedValue . grammarV1Declaration . locatedValue)
        (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- declarations]
      components = [c | GrammarV1ComponentDeclaration c <- declarations]
      programs = [p | GrammarV1ProgramDeclaration p <- declarations]
  case (protocols, components, programs) of
    ([protocol], [client, server], [_]) -> Right (protocol, client, server)
    other -> Left ("restricted source fixture shape was not parsed: " <> show other)

fixture :: Text -> Either String Fixture
fixture = fixtureWithMessageBinder Nothing

-- The independently authorized protocol's message binder must correspond to
-- the receiver's *resolved source* binder, not its display spelling. The
-- optional deliberately wrong binder is used only for a negative witness.
fixtureWithMessageBinder :: Maybe Name -> Text -> Either String Fixture
fixtureWithMessageBinder alternateMessageBinder source = do
  (protocol, senderSource, receiverSource) <- parseParts source
  (sourceFamily, _) <- case grammarV1CheckedBinaryProtocolFamily emptyStaticContext
      protocolRoot (InterfaceRevision "fsem02.restricted.source.v1") protocol of
    Nothing -> Left "Bytes[8] source protocol is outside checked family competence"
    Just (Left err) -> Left ("source protocol was rejected: " <> show err)
    Just (Right value) -> Right value
  -- A concrete restricted Bytes message does NOT confer Message authority.
  -- Confirm the source family is rejected without a boundary certificate.
  case instantiateBinaryProtocol strictGenericInstantiationPolicy sourceFamily [] [] of
    Left (ProtocolConcreteMessageRequiresBoundaryContract exactType)
      | exactType == payloadTy -> Right ()
    other -> Left ("bare concrete restricted source was admitted: " <> show other)
  receiver <- case grammarV1CheckedComponentReceiveClose receiverRoot receiverSource of
    Just (Right value) -> Right value
    other -> Left ("parsed source receiver body not checked: " <> show other)
  let receiveBinder = grammarV1ResolvedBinderCoreName
        (checkedComponentReceivePayload receiver)
  -- Protocol/message identity and the boundary contract are explicit external
  -- trusted inputs; not synthesized from source spelling or Bytes syntax.
  -- This test's separately authorized protocol chooses the exact checked
  -- receiver binder; the Core checker rejects any other binder. This is a
  -- *premise*, not proof of general source/protocol alpha-renaming.
  let messageKey = GenericStaticParameterKey "Payload"
      payloadSemantics = SemanticAtom "fsem02.external.restricted-payload"
      family = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = protocolRoot
        , protocolFamilyInterfaceRevision =
            InterfaceRevision (case alternateMessageBinder of
              Nothing -> "fsem02.external.authorized.v1"
              Just _ -> "fsem02.external.mismatched-binder.v1")
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = clientRole
        , protocolFamilyPeerRole = serverRole
        , protocolFamilyPrimarySession = ProtocolTemplateSend
            (maybe receiveBinder id alternateMessageBinder)
            (ProtocolParameterType messageKey)
            (ProtocolTemplateEnd doneOutcome)
        }
      argument = ProtocolMessageArgument
        { protocolMessageArgumentKey = messageKey
        , protocolMessageArgumentType = payloadTy
        , protocolMessageArgumentSemantics = payloadSemantics
        , protocolMessageArgumentBoundaryContract = BoundaryMessageContract
            { boundaryMessageContractRevision = "fsem02.external.owned.v1"
            , boundaryMessageContractType = payloadTy
            , boundaryMessageContractSemantics = payloadSemantics
            , boundaryMessageContractShape =
                BoundaryMessageAdmittedLeaf "external-restricted-message"
            }
        }
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [argument] []
  sender <- case grammarV1CheckedComponentSendClose senderRoot senderSource of
    Just (Right value) -> Right value
    other -> Left ("parsed source sender body not checked: " <> show other)
  let clientEndpoint = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint sender)
      serverEndpoint = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint receiver)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor sender)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor receiver)
      payloadOwner = grammarV1ResolvedBinderCoreName
        (checkedComponentSendPayload sender)
      payloadReceiver = grammarV1ResolvedBinderCoreName
        (checkedComponentReceivePayload receiver)
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  graph <- mapLeft show $ instantiateArchitecture rootKey rootSpec
  unactivated <- mapLeft show $
    elaborateProcessNetwork graph [clientSite, serverSite]
  let rootRevision = identityInstanceRevision (processNetworkRoot unactivated)
      clientProcess = deriveProcessKey rootRevision (processSiteKey clientSite)
      serverProcess = deriveProcessKey rootRevision (processSiteKey serverSite)
      clientBindings =
        [ activationBinding clientEndpointOccurrence clientEndpoint Linear
            (TyEndpoint (protocolProjectionSession clientProjection))
            (ProtocolEndpointOrigin "external.source.client")
        , activationBinding payloadOccurrence payloadOwner Linear payloadTy
            (TargetParameterOrigin "external.source.payload")
        , activationBinding spectatorOccurrence spectatorName Affine TyBool
            (TargetParameterOrigin "external.source.spectator")
        ]
      serverBindings =
        [ activationBinding serverEndpointOccurrence serverEndpoint Linear
            (TyEndpoint (protocolProjectionSession serverProjection))
            (ProtocolEndpointOrigin "external.source.server")
        ]
  (network, activation) <- mapLeft show $ activateProcessState unactivated
    [ ProcessActivationContract clientProcess clientBindings
    , ProcessActivationContract serverProcess serverBindings
    ]
  clientResources <- requireResource clientProcess activation
  serverResources <- requireResource serverProcess activation
  let revision = binaryProtocolInstanceRevision instanceValue
      clientContext = ProtocolContext
        { protocolResources = clientResources
        , protocolEndpoints = Map.singleton clientEndpoint ProtocolEndpointBinding
            { protocolEndpointName = clientEndpoint
            , protocolEndpointInstance = revision
            , protocolEndpointRole = clientRole
            , protocolEndpointSession = protocolProjectionSession clientProjection
            }
        }
      serverContext = ProtocolContext
        { protocolResources = serverResources
        , protocolEndpoints = Map.singleton serverEndpoint ProtocolEndpointBinding
            { protocolEndpointName = serverEndpoint
            , protocolEndpointInstance = revision
            , protocolEndpointRole = serverRole
            , protocolEndpointSession = protocolProjectionSession serverProjection
            }
        }
  state <- mapLeft show $ communicationStateFromActivation activation
    (Map.fromList [(clientProcess, clientContext), (serverProcess, serverContext)])
  Right Fixture
    { fxSender = senderSource, fxReceiver = receiverSource
    , fxInstance = instanceValue, fxNetwork = network, fxBefore = state
    , fxClientProcess = clientProcess, fxServerProcess = serverProcess
    , fxClientOld = clientEndpoint, fxServerOld = serverEndpoint
    , fxClientNext = clientNext, fxServerNext = serverNext
    , fxPayloadOwner = payloadOwner, fxPayloadReceiver = payloadReceiver
    }

checked :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ProcessCommunicationState
  -> Either GrammarV1RestrictedSourceError GrammarV1RestrictedSourceTransition
checked fx sender receiver state =
  grammarV1CheckRestrictedSourceRendezvous
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx) payloadOccurrence
    (fxNetwork fx) state

acceptedReplay :: Fixture -> Either String ()
acceptedReplay fx = do
  first <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  second <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  assert (first == second) "same checked source and state produced different replays"
  let next = restrictedSourceNext first
      owners = communicationRestrictedOwners next
      beforeOwners = communicationRestrictedOwners (fxBefore fx)
      request = restrictedSourceRequest first
      transfer = restrictedSourceTransfer first
  assert (restrictedMessageOccurrence transfer == payloadOccurrence
       && restrictedMessageMode transfer == Linear
       && restrictedMessageType transfer == payloadTy
       && restrictedMessageSenderName transfer == fxPayloadOwner fx
       && restrictedMessageReceiverName transfer == fxPayloadReceiver fx)
    "source payload binder/type/mode/occurrence drifted"
  assert (request == SendReceiveRendezvous
          (ProcessRendezvousSide (fxClientProcess fx) (fxClientOld fx)
            (fxClientNext fx) (binaryProtocolInstanceRevision (fxInstance fx)) clientRole)
          (ProcessRendezvousSide (fxServerProcess fx) (fxServerOld fx)
            (fxServerNext fx) (binaryProtocolInstanceRevision (fxInstance fx)) serverRole))
    "source-derived exact rendezvous endpoint request drifted"
  assert (Map.keysSet owners == Map.keysSet beforeOwners)
    "restricted transfer created or dropped occurrence keys"
  assert (Map.lookup payloadOccurrence owners
          == Just (fxServerProcess fx, fxPayloadReceiver fx)
       && Map.lookup clientEndpointOccurrence owners
          == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverEndpointOccurrence owners
          == Just (fxServerProcess fx, fxServerNext fx))
    "restricted payload and endpoint identities did not progress exactly"
  assert (Map.lookup spectatorOccurrence owners
       == Map.lookup spectatorOccurrence beforeOwners)
    "independent affine spectator changed owner"
  senderContext <- requireProtocol (fxClientProcess fx) next
  receiverContext <- requireProtocol (fxServerProcess fx) next
  assert (Map.notMember (fxPayloadOwner fx)
            (linearBindings (protocolResources senderContext)))
    "sender retained consumed linear payload"
  assert (Map.lookup (fxPayloadReceiver fx)
            (linearBindings (protocolResources receiverContext)) == Just payloadTy)
    "receiver missing exact linear payload"
  assert (Map.lookup spectatorName (affineBindings (protocolResources senderContext))
       == Just TyBool) "spectator's affine resource was modified"
  assert (Map.notMember (fxClientOld fx) (protocolEndpoints senderContext)
       && Map.notMember (fxServerOld fx) (protocolEndpoints receiverContext)
       && Map.lookup (fxClientNext fx) (protocolEndpoints senderContext)
          == Just (ProtocolEndpointBinding (fxClientNext fx)
               (binaryProtocolInstanceRevision (fxInstance fx))
               clientRole (End doneOutcome))
       && Map.lookup (fxServerNext fx) (protocolEndpoints receiverContext)
          == Just (ProtocolEndpointBinding (fxServerNext fx)
               (binaryProtocolInstanceRevision (fxInstance fx))
               serverRole (End doneOutcome)))
    "exact consumed endpoints did not become fresh terminal successors"

staleOwnerRejects :: Fixture -> Either String ()
staleOwnerRejects fx = do
  first <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case checked fx (fxSender fx) (fxReceiver fx) (restrictedSourceNext first) of
    Left (RestrictedSourceCoreError
      (RestrictedMessageOwnerMismatch key _ _ actualProcess actualName)) ->
        assert (key == payloadOccurrence
             && actualProcess == fxServerProcess fx
             && actualName == fxPayloadReceiver fx)
          "stale rejection did not preserve transferred owner identity"
    other -> Left ("reused stale source predecessor: " <> show other)

missingOwnerRejects :: Fixture -> Either String ()
missingOwnerRejects fx =
  let before = fxBefore fx
      missing = before { communicationRestrictedOwners =
        Map.delete payloadOccurrence (communicationRestrictedOwners before) }
  in case checked fx (fxSender fx) (fxReceiver fx) missing of
    Left (RestrictedSourceCoreError (RestrictedMessageOwnerUnknown key)) ->
      assert (key == payloadOccurrence) "missing owner diagnostic changed occurrence"
    other -> Left ("manufactured missing restricted payload: " <> show other)

duplicateReceiverRejects :: Fixture -> Either String ()
duplicateReceiverRejects fx = do
  before <- requireProtocol (fxServerProcess fx) (fxBefore fx)
  duplicate <- mapLeft show $ insertBinding Linear
    (fxPayloadReceiver fx) payloadTy (protocolResources before)
  let changed = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) (before { protocolResources = duplicate })
          (communicationProtocolContexts (fxBefore fx)) }
  case checked fx (fxSender fx) (fxReceiver fx) changed of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
        assert (process == fxServerProcess fx && name == fxPayloadReceiver fx)
          "receiver duplicate diagnostic lost source binder/process"
    other -> Left ("duplicate receiving resource was admitted: " <> show other)

wrongSourceCloseRejects :: Fixture -> Text -> Either String ()
wrongSourceCloseRejects fx source = do
  (_, rejected, _) <- parseParts source
  case checked fx rejected (fxReceiver fx) (fxBefore fx) of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("minimally rejected source close changed error: " <> show other)

wrongSourcePayloadModeRejects :: Fixture -> Text -> Either String ()
wrongSourcePayloadModeRejects fx source = do
  let bad = Text.replace "payload : Bytes[8]" "payload : U8" source
  (_, rejected, _) <- parseParts bad
  case checked fx rejected (fxReceiver fx) (fxBefore fx) of
    Left (RestrictedSourcePayloadModeNotRestricted Unrestricted) -> Right ()
    other -> Left ("unrestricted source payload entered restricted transfer: " <> show other)

wrongWrittenReceiveTypeRejects :: Fixture -> Text -> Either String ()
wrongWrittenReceiveTypeRejects fx source = do
  let bad = Text.replace "receive Bytes[8] on endpoint"
        "receive U8 on endpoint" source
  (_, _, rejected) <- parseParts bad
  case checked fx (fxSender fx) rejected (fxBefore fx) of
    Left (RestrictedSourceMessageTypeMismatch expected actual) ->
      assert (expected == payloadTy && actual == TyUInt 8)
        "written receiver type mismatch lost exact Types"
    other -> Left ("wrong source receive type admitted: " <> show other)

wrongProtocolBinderRejects :: Text -> Either String ()
wrongProtocolBinderRejects source = do
  fx <- fixtureWithMessageBinder (Just (Name "value")) source
  case checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx) of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverBinderMismatch expected actual)) ->
        assert (expected == Name "value" && actual == fxPayloadReceiver fx)
          "protocol receiver-binder mismatch lost exact checked source identity"
    other -> Left ("unmatched external protocol binder was admitted: " <> show other)

wrongSessionHeadRejects :: Fixture -> Either String ()
wrongSessionHeadRejects fx = do
  sender <- requireProtocol (fxClientProcess fx) (fxBefore fx)
  let old = fxClientOld fx
      existing = protocolEndpoints sender
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) clientRole
        (End doneOutcome)
      changed = sender { protocolEndpoints = Map.insert old wrong existing }
      before = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) changed
          (communicationProtocolContexts (fxBefore fx)) }
  case checked fx (fxSender fx) (fxReceiver fx) before of
    Left (RestrictedSourceCoreError (RendezvousProtocolError process _)) ->
      assert (process == fxClientProcess fx)
        "wrong head error lost sender identity"
    other -> Left ("incorrect live send session head admitted: " <> show other)

requireProtocol :: ProcessKey -> ProcessCommunicationState -> Either String ProtocolContext
requireProtocol process state =
  maybe (Left "missing expected process protocol context") Right
    (Map.lookup process (communicationProtocolContexts state))

requireResource :: ProcessKey -> ProcessActivationState -> Either String ResourceContext
requireResource process activation =
  maybe (Left "missing expected activated resource context") Right
    (Map.lookup process (activationProcessContexts activation))

activationBinding
  :: ActivationOccurrenceKey -> Name -> Mode -> Ty
  -> ActivationBindingOrigin -> ActivationBinding
activationBinding occurrence name mode ty origin = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = name
  , activationCheckedTypeMode = CheckedTypeMode ty mode
  , activationBindingOrigin = origin
  , activationReachability = DirectStatefulReachability occurrence
  , activationStartsSharedLoan = False
  }

payloadTy :: Ty
payloadTy = TyBytes (RefNat 8)

doneOutcome :: Outcome
doneOutcome = Outcome "Done"

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

senderRoot, receiverRoot, protocolRoot :: DeclarationKey
senderRoot = DeclarationKey "component.fsem02.ClientWorker"
receiverRoot = DeclarationKey "component.fsem02.ServerWorker"
protocolRoot = DeclarationKey "protocol.fsem02.OwnedPing"

payloadOccurrence, clientEndpointOccurrence, serverEndpointOccurrence, spectatorOccurrence
  :: ActivationOccurrenceKey
payloadOccurrence = ActivationOccurrenceKey "fsem02.external.entry.payload"
clientEndpointOccurrence = ActivationOccurrenceKey "fsem02.external.client.endpoint"
serverEndpointOccurrence = ActivationOccurrenceKey "fsem02.external.server.endpoint"
spectatorOccurrence = ActivationOccurrenceKey "fsem02.external.spectator"

spectatorName :: Name
spectatorName = Name "spectator"

clientSite, serverSite :: ProcessDeclarationSite
clientSite = ProcessDeclarationSite (ProcessSiteKey "fsem02-client-site") clientTarget
serverSite = ProcessDeclarationSite (ProcessSiteKey "fsem02-server-site") serverTarget

rootKey, clientTarget, serverTarget :: InstanceKey
rootKey = InstanceKey "fsem02-root"
clientTarget = scopedInstanceKey rootKey clientSlot
serverTarget = scopedInstanceKey rootKey serverSlot

clientSlot, serverSlot :: OccurrenceSlotKey
clientSlot = OccurrenceSlotKey "fsem02-client-slot"
serverSlot = OccurrenceSlotKey "fsem02-server-slot"

rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ArchitectureChildSpec clientSlot workerSpec
      ,ArchitectureChildSpec serverSlot workerSpec]
  , architectureNodeReferences = []
  }

workerSpec :: ArchitectureNodeSpec
workerSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "worker"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren = []
  , architectureNodeReferences = []
  }

declaration :: Text -> DeclarationIdentity
declaration label = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation
      { declarationDisplayName = label, declarationModulePath = [] }
  , declarationKey = DeclarationKey ("fsem02." <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False err = Left err

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

-- Execute the two actual source close statements against the exact post-
-- rendezvous state, not against a fresh or guessed endpoint context.
closeFromSource
  :: Fixture
  -> GrammarV1ComponentDecl
  -> GrammarV1ComponentDecl
  -> GrammarV1RestrictedSourceTransition
  -> ProtocolRoleKey
  -> ProtocolRoleKey
  -> Outcome
  -> Outcome
  -> Either GrammarV1RestrictedSourceCloseError GrammarV1RestrictedSourceCloseTransition
closeFromSource fx sender receiver rendezvous senderRole receiverRole
    senderOutcome receiverOutcome =
  grammarV1CheckRestrictedSourceClose
    senderRoot sender receiverRoot receiver
    (fxNetwork fx) rendezvous
    (fxClientProcess fx) (fxServerProcess fx)
    (binaryProtocolInstanceRevision (fxInstance fx))
    senderRole receiverRole senderOutcome receiverOutcome

sourceCloseReplay :: Fixture -> Either String ()
sourceCloseReplay fx = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  first <- mapLeft show $ closeFromSource fx (fxSender fx) (fxReceiver fx)
    rendezvous clientRole serverRole doneOutcome doneOutcome
  second <- mapLeft show $ closeFromSource fx (fxSender fx) (fxReceiver fx)
    rendezvous clientRole serverRole doneOutcome doneOutcome
  assert (first == second) "two source close replays were nondeterministic"
  let before = restrictedSourceNext rendezvous
      next = restrictedSourceCloseNext first
      beforeOwners = communicationRestrictedOwners before
      owners = communicationRestrictedOwners next
  assert (restrictedSourceClosedSender first == fxClientNext fx
       && restrictedSourceClosedReceiver first == fxServerNext fx)
    "source closes changed their resolved successor identities"
  assert (owners == Map.delete clientEndpointOccurrence
            (Map.delete serverEndpointOccurrence beforeOwners))
    "source closes did not retire exactly the two endpoint occurrence keys"
  assert (Map.lookup payloadOccurrence owners
          == Just (fxServerProcess fx, fxPayloadReceiver fx)
       && Map.lookup spectatorOccurrence owners
          == Map.lookup spectatorOccurrence beforeOwners)
    "source closes modified payload or spectator ownership"
  sender <- requireProtocol (fxClientProcess fx) next
  receiver <- requireProtocol (fxServerProcess fx) next
  assert (Map.notMember (fxClientNext fx) (protocolEndpoints sender)
       && Map.notMember (fxServerNext fx) (protocolEndpoints receiver)
       && Map.notMember (fxClientNext fx)
            (linearBindings (protocolResources sender))
       && Map.notMember (fxServerNext fx)
            (linearBindings (protocolResources receiver)))
    "closed successors are still live in protocol or resource contexts"
  assert (Map.lookup (fxPayloadReceiver fx)
            (linearBindings (protocolResources receiver)) == Just payloadTy
       && Map.lookup spectatorName
            (affineBindings (protocolResources sender)) == Just TyBool)
    "endpoint close improperly discharged payload or independent spectator"
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      (rendezvous { restrictedSourceNext = next })
      clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseSenderCoreError
      (EndpointClosureOccurrenceUnknown process endpoint)) ->
        assert (process == fxClientProcess fx && endpoint == fxClientNext fx)
          "replayed source close did not identify the stale predecessor"
    other -> Left ("second close was permitted: " <> show other)


-- Core closure alone must not authenticate a forged cached request.
sourceCloseRejectsForgedRequest :: Fixture -> Either String ()
sourceCloseRejectsForgedRequest fx = do
  rendezvous <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  let expected = restrictedSourceRequest rendezvous
      altered = case expected of
        SendReceiveRendezvous sender receiver ->
          SendReceiveRendezvous
            (sender { rendezvousProcess = fxServerProcess fx }) receiver
        other -> other
  assert (expected /= altered) "forged request did not differ from source"
  let forged = rendezvous { restrictedSourceRequest = altered }
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      forged clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseRequestMismatch checkedRequest actualRequest) ->
      assert (checkedRequest == expected && actualRequest == altered)
        "forged rendezvous request lost exact expected/actual identities"
    other -> Left ("forged source rendezvous request was admitted: " <> show other)

sourceCloseRejectsForgedPayloadBinder :: Fixture -> Either String ()
sourceCloseRejectsForgedPayloadBinder fx = do
  rendezvous <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  let transfer = restrictedSourceTransfer rendezvous
      forgedName = Name "fsem02.forged.payload-owner"
      forgedTransfer = transfer { restrictedMessageSenderName = forgedName }
      forged = rendezvous { restrictedSourceTransfer = forgedTransfer }
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      forged clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseTransferBinderMismatch
      sourceSender sourceReceiver actualSender actualReceiver) ->
      assert (sourceSender == fxPayloadOwner fx
           && sourceReceiver == fxPayloadReceiver fx
           && actualSender == forgedName
           && actualReceiver == fxPayloadReceiver fx)
        "forged sender payload projection lost source binder provenance"
    other -> Left ("forged source payload binder was admitted: " <> show other)

sourceCloseRejectsForgedReceiveBinder :: Fixture -> Either String ()
sourceCloseRejectsForgedReceiveBinder fx = do
  rendezvous <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  let transfer = restrictedSourceTransfer rendezvous
      forgedName = Name "fsem02.forged.received-owner"
      forgedTransfer = transfer { restrictedMessageReceiverName = forgedName }
      forged = rendezvous { restrictedSourceTransfer = forgedTransfer }
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      forged clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseTransferBinderMismatch
      sourceSender sourceReceiver actualSender actualReceiver) ->
      assert (sourceSender == fxPayloadOwner fx
           && sourceReceiver == fxPayloadReceiver fx
           && actualSender == fxPayloadOwner fx
           && actualReceiver == forgedName)
        "forged receiver payload projection lost source binder provenance"
    other -> Left ("forged source receiver binder was admitted: " <> show other)

sourceCloseRejectedSpelling :: Fixture -> Text -> Either String ()
sourceCloseRejectedSpelling fx rejected = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  (_, wrongSender, _) <- parseParts rejected
  case closeFromSource fx wrongSender (fxReceiver fx)
      rendezvous clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseSenderError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("stale close source was admitted by close execution: " <> show other)

sourceCloseMissingServerOwner :: Fixture -> Either String ()
sourceCloseMissingServerOwner fx = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  let before = restrictedSourceNext rendezvous
      owners = communicationRestrictedOwners before
      state = before { communicationRestrictedOwners =
        Map.delete serverEndpointOccurrence owners }
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      (rendezvous { restrictedSourceNext = state })
      clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseReceiverCoreError
      (EndpointClosureOccurrenceUnknown process endpoint)) ->
        assert (process == fxServerProcess fx && endpoint == fxServerNext fx)
          "missing receiver close owner was misclassified"
    other -> Left ("receiver endpoint with missing owner was closed: " <> show other)

sourceCloseWrongOutcome :: Fixture -> Either String ()
sourceCloseWrongOutcome fx = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  let incorrect = Outcome "NotDone"
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      rendezvous clientRole serverRole doneOutcome incorrect of
    Left (RestrictedSourceCloseReceiverCoreError
      (EndpointClosureProtocolError process
        (ProtocolSessionError (CloseOutcomeMismatch expected actual)))) ->
        assert (process == fxServerProcess fx
             && expected == doneOutcome && actual == incorrect)
          "wrong terminal outcome lost exact session error class"
    other -> Left ("mismatched receiver close outcome was admitted: " <> show other)

sourceCloseWrongHead :: Fixture -> Either String ()
sourceCloseWrongHead fx = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  receiver <- requireProtocol (fxServerProcess fx) (restrictedSourceNext rendezvous)
  let old = fxServerNext fx
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) serverRole
        (End (Outcome "WrongHead"))
      changed = receiver { protocolEndpoints = Map.insert old wrong
        (protocolEndpoints receiver) }
      before = restrictedSourceNext rendezvous
      tampered = before { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) changed
          (communicationProtocolContexts before) }
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      (rendezvous { restrictedSourceNext = tampered })
      clientRole serverRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseReceiverCoreError
      (EndpointClosureProtocolError process
        (ProtocolEndpointSessionMismatch name _ _))) ->
        assert (process == fxServerProcess fx && name == old)
          "wrong terminal session head lost exact error provenance"
    other -> Left ("incorrect terminal session head was admitted: " <> show other)

sourceCloseWrongRole :: Fixture -> Either String ()
sourceCloseWrongRole fx = do
  rendezvous <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case closeFromSource fx (fxSender fx) (fxReceiver fx)
      rendezvous clientRole clientRole doneOutcome doneOutcome of
    Left (RestrictedSourceCloseReceiverCoreError
      (EndpointClosureProtocolError process
        (ProtocolRoleMismatch name _ _))) ->
        assert (process == fxServerProcess fx && name == fxServerNext fx)
          "incorrect terminal role did not preserve endpoint identity"
    other -> Left ("receiver source close accepted the wrong nominal role: " <> show other)


-- The actual source is first parsed/checked, then sent/received and closed.
-- The residual payload and independent activation spectator are NOT silently
-- consumed by source 'close'. This separate boundary requires explicit
-- terminal declarations, dispositions, obligation and root inputs.
terminalPrefix
  :: Fixture
  -> Either String
       (GrammarV1RestrictedSourceTransition,
        GrammarV1RestrictedSourceCloseTransition)
terminalPrefix fx = do
  rendezvous <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  closed <- mapLeft show $
    closeFromSource fx (fxSender fx) (fxReceiver fx) rendezvous
      clientRole serverRole doneOutcome doneOutcome
  pure (rendezvous, closed)

senderTerminalPlan :: Fixture -> DeclaredTerminalTransition
senderTerminalPlan fx =
  DeclaredTerminalTransition (fxClientProcess fx)
    (Closed doneOutcome) [spectatorName]

receiverTerminalPlan :: Fixture -> DeclaredTerminalTransition
receiverTerminalPlan fx =
  DeclaredTerminalTransition (fxServerProcess fx)
    (Closed doneOutcome) [fxPayloadReceiver fx]

emptyRootResidue :: RootClosureState
emptyRootResidue = RootClosureState Set.empty Set.empty Set.empty

terminalCheck
  :: Fixture
  -> GrammarV1RestrictedSourceTransition
  -> GrammarV1RestrictedSourceCloseTransition
  -> DeclaredTerminalTransition
  -> DeclaredTerminalTransition
  -> Map.Map ProcessKey (Set.Set ObligationId)
  -> RootClosureState
  -> Either GrammarV1RestrictedSourceTerminalError
       GrammarV1RestrictedSourceTerminalTransition
terminalCheck fx rendezvous closed sender receiver obligations root =
  grammarV1CheckRestrictedSourceTerminal (fxNetwork fx) rendezvous closed
    sender receiver doneOutcome doneOutcome obligations root

sourceTerminalReplay :: Fixture -> Either String ()
sourceTerminalReplay fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let sender = senderTerminalPlan fx
      receiver = receiverTerminalPlan fx
      replay = terminalCheck fx rendezvous closed sender receiver
        Map.empty emptyRootResidue
  first <- mapLeft show replay
  second <- mapLeft show replay
  assert (first == second) "terminal source-prefix replay was nondeterministic"
  let runtime = restrictedSourceTerminalRuntime first
      fact = restrictedSourceTerminalFact first
  assert (Map.null (restrictedSourceTerminalRemainingOwners first))
    "terminal success left activation-owned resource occurrences"
  assert (Map.keysSet (rootTerminalProcesses fact) ==
            Set.fromList [fxClientProcess fx, fxServerProcess fx])
    "root terminal fact does not cover exactly the activated processes"
  assert (Map.lookup (fxClientProcess fx) (runtimeStatuses runtime) ==
            Just (ProcessTerminal (ProcessTerminalFact
              (fxClientProcess fx) (Closed doneOutcome)))
       && Map.lookup (fxServerProcess fx) (runtimeStatuses runtime) ==
            Just (ProcessTerminal (ProcessTerminalFact
              (fxServerProcess fx) (Closed doneOutcome))))
    "declared terminal facts did not retain the exact external outcomes"
  contexts <- maybe (Left "sender terminal context missing") Right
    (Map.lookup (fxClientProcess fx) (runtimeProtocolContexts runtime))
  peer <- maybe (Left "receiver terminal context missing") Right
    (Map.lookup (fxServerProcess fx) (runtimeProtocolContexts runtime))
  assert (Map.null (linearBindings (protocolResources contexts))
       && Map.null (affineBindings (protocolResources contexts))
       && Map.null (linearBindings (protocolResources peer))
       && Map.null (protocolEndpoints contexts)
       && Map.null (protocolEndpoints peer))
    "terminal resource contexts retain explicitly disposed owners"

sourceTerminalNegativeGates :: Fixture -> Either String ()
sourceTerminalNegativeGates fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let sender = senderTerminalPlan fx
      receiver = receiverTerminalPlan fx
      run s r obligations root =
        terminalCheck fx rendezvous closed s r obligations root
  case run sender (receiver { declaredTerminalDisposals = [] })
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalReceiverError
      (TerminalResourceError process (UnconsumedLinearResources remaining))) ->
        assert (process == fxServerProcess fx
             && Map.lookup (fxPayloadReceiver fx) remaining == Just payloadTy)
          "missing payload disposition lost exact linear debt"
    other -> Left ("live restricted payload was silently dropped: " <> show other)
  case run (sender { declaredTerminalDisposals = [] }) receiver
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalUnaccountedOwner occurrence process name) ->
      assert (occurrence == spectatorOccurrence
           && process == fxClientProcess fx && name == spectatorName)
        "unaccounted affine spectator did not block root closure"
    other -> Left ("undisposed affine spectator was ignored: " <> show other)
  case run sender (receiver { declaredTerminalDisposals =
      [fxPayloadReceiver fx, fxPayloadReceiver fx] })
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalReceiverError
      (DuplicateTerminalDisposal name)) ->
      assert (name == fxPayloadReceiver fx)
        "duplicate declared disposal lost exact identity"
    other -> Left ("duplicate terminal payload disposal admitted: " <> show other)
  case run sender (receiver { declaredTerminalDisposals = [Name "absent"] })
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalReceiverError
      (TerminalDisposalUnknown process name (UnknownBinding missing))) ->
      assert (process == fxServerProcess fx && name == Name "absent"
           && missing == Name "absent")
        "unknown terminal disposal changed diagnostic"
    other -> Left ("invented resource was disposed: " <> show other)
  case run sender receiver
      (Map.singleton (fxServerProcess fx)
        (Set.singleton (ObligationId "undischarged"))) emptyRootResidue of
    Left (RestrictedSourceTerminalReceiverError
      (TerminalOpenObligations process open)) ->
      assert (process == fxServerProcess fx
           && open == Set.singleton (ObligationId "undischarged"))
        "external assurance obligation was silently discharged"
    other -> Left ("open assurance obligation permitted terminal fact: " <> show other)
  case run sender receiver Map.empty
      (emptyRootResidue { rootOpenResources = Set.singleton (Name "root-live") }) of
    Left (RestrictedSourceTerminalRootError (RootTerminalOpenResources open)) ->
      assert (open == Set.singleton (Name "root-live"))
        "root residue disappeared from rejection"
    other -> Left ("nonempty root residue permitted terminal fact: " <> show other)
  case run (sender { declaredTerminalControl = Continue }) receiver
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalWrongControl process Continue expected) ->
      assert (process == fxClientProcess fx && expected == doneOutcome)
        "undeclared terminal control was accepted"
    other -> Left ("Continue was treated as source terminal: " <> show other)
  let before = restrictedSourceCloseNext closed
      tampered = before { communicationRestrictedOwners =
        Map.delete payloadOccurrence (communicationRestrictedOwners before) }
  case terminalCheck fx rendezvous
      (closed { restrictedSourceCloseNext = tampered })
      sender receiver Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalPayloadOwnerMismatch occurrence Nothing) ->
      assert (occurrence == payloadOccurrence)
        "lost payload occurrence was silently reconstructed"
    other -> Left ("missing post-close payload was accepted: " <> show other)
  case terminalCheck fx rendezvous
      (closed { restrictedSourceClosedSender = Name "not-the-successor" })
      sender receiver Map.empty emptyRootResidue of
    Left RestrictedSourceTerminalCloseIdentityMismatch -> Right ()
    other -> Left ("tampered source-close successor was accepted: " <> show other)

-- The terminal adapter must not accept a post-close state manufactured by a
-- caller, even when it preserves both successor spellings and the exact
-- payload occurrence. A forged affine resource is not an authorized disposal.
sourceTerminalRejectForgedClosedState :: Fixture -> Either String ()
sourceTerminalRejectForgedClosedState fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let before = restrictedSourceCloseNext closed
  sender <- requireProtocol (fxClientProcess fx) before
  forgedResources <- mapLeft show $ insertBinding Affine
    (Name "forged-unowned") TyBool (protocolResources sender)
  let forgedSender = sender { protocolResources = forgedResources }
      forged = before { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) forgedSender
          (communicationProtocolContexts before) }
      closedForgery = closed { restrictedSourceCloseNext = forged }
  case terminalCheck fx rendezvous closedForgery
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      Map.empty emptyRootResidue of
    Left RestrictedSourceTerminalCloseStateMismatch -> Right ()
    other -> Left ("forged post-close resource state was accepted: " <> show other)

-- Missing a predecessor owner in the rendezvous successor must be rejected
-- by native close replay, not silently reconstructed from the supplied
-- post-close carrier.
sourceTerminalRejectStaleSenderReplay :: Fixture -> Either String ()
sourceTerminalRejectStaleSenderReplay fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let before = restrictedSourceNext rendezvous
      stale = before { communicationRestrictedOwners =
        Map.delete clientEndpointOccurrence (communicationRestrictedOwners before) }
      altered = rendezvous { restrictedSourceNext = stale }
  case terminalCheck fx altered closed
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalCloseReplaySenderError
      (EndpointClosureOccurrenceUnknown process endpoint)) ->
        assert (process == fxClientProcess fx && endpoint == fxClientNext fx)
          "sender replay error lost exact process/endpoint provenance"
    other -> Left ("stale sender replay was accepted: " <> show other)

sourceTerminalRejectStaleReceiverReplay :: Fixture -> Either String ()
sourceTerminalRejectStaleReceiverReplay fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let before = restrictedSourceNext rendezvous
      stale = before { communicationRestrictedOwners =
        Map.delete serverEndpointOccurrence (communicationRestrictedOwners before) }
      altered = rendezvous { restrictedSourceNext = stale }
  case terminalCheck fx altered closed
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalCloseReplayReceiverError
      (EndpointClosureOccurrenceUnknown process endpoint)) ->
        assert (process == fxServerProcess fx && endpoint == fxServerNext fx)
          "receiver replay error lost exact process/endpoint provenance"
    other -> Left ("stale receiver replay was accepted: " <> show other)
