{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Context (CheckError (..), ResourceContext (..), endSharedLoan, insertBinding, startSharedLoan)
import Phil.Core.Generic (GenericStaticParameterKey (..), strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessRendezvous
import Phil.Core.ProcessEndpointClosure
  ( ProcessEndpointClosureError (..), closeProcessEndpointState )
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
import Phil.Surface.GrammarV1.ComponentRestrictedTerminalHead
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
          , receiverBinderDisplayRenamePreservesAuthorityBoundary accepted
          , senderBinderDisplayRenamePreservesActivationBoundary accepted
          , dualBinderDisplayCollisionKeepsAuthorityDisjoint accepted
          , dualAuthorityErrorPriority accepted
          , projectedHeadBinderPriority accepted
          , binderResourceAtomicityPriority accepted
          , senderResourceTypeBeforeReceiverSlot accepted
          , crossModeReceiverNameCollision accepted
          , borrowedSenderTransferRefusal accepted
          , borrowedEndpointPrefixPriority accepted
          , borrowedOccupiedReceiverCollision accepted
          , crossModeSenderPayloadRefusal accepted
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
          , sourceCloseDiamondReplay fx
          , sourceSuccessorTraceReplay fx
          , sourceClosePrefixReplay fx
          , typedHeadAccepted fx
          , typedHeadRejectedSource fx rejected
          , typedHeadWrongOutcome fx
          , typedHeadWrongSessionHead fx
          , typedHeadStaleOriginal fx
          , typedPrefixAccepted fx
          , typedPrefixRejectedSource fx rejected
          , typedPrefixWrongOutcome fx
          , typedPrefixWrongSessionHead fx
          , typedPrefixStaleOriginal fx
          , typedPrefixAliasedOccurrence fx
          , sourceClosePrefixRejectedSource fx rejected
          , sourceClosePrefixStalePredecessor fx
          , sourceClosePrefixWrongOutcome fx
          , sourceClosePrefixRepeatRetirement fx
          , sourceSuccessorTraceAlphaRename fx accepted
          , sourceSuccessorTraceRejectedSource fx rejected
          , sourceSuccessorTraceWrongOccurrence fx
          , sourceSuccessorTraceAliasedOccurrence fx
          , sourceCloseDiamondRejectedSource fx rejected
          , sourceCloseDiamondStalePredecessor fx
          , sourceCloseDiamondWrongSessionHead fx
          , sourceCloseDiamondWrongOutcome fx
          , sourceCloseDiamondReceiverFirstStale fx
          , sourceTerminalReplay fx
          , sourceTerminalNegativeGates fx
          , sourceTerminalRejectForgedClosedState fx
          , sourceTerminalRejectStaleSenderReplay fx
          , sourceTerminalRejectStaleReceiverReplay fx
          , sourceTerminalRejectForgedRendezvousState fx
          , sourceTerminalRejectMissingPredecessorOwner fx
          , sourceTerminalRejectWrongPredecessorHead fx
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

-- Renaming only the source receiver's DISPLAY binder does not replace its
-- declaration-rooted semantic identity. A separately authorized protocol
-- with that exact resolved identity still progresses, while a protocol
-- using the bare source-level display name is rejected by the native Core
-- receiver-binder check. No nominal authority is inferred by this test.
receiverBinderDisplayRenamePreservesAuthorityBoundary :: Text -> Either String ()
receiverBinderDisplayRenamePreservesAuthorityBoundary source = do
  let original = "let (done, received) = receive Bytes[8] on endpoint;"
      renamed = "let (done, delivery) = receive Bytes[8] on endpoint;"
      renamedSource = Text.replace original renamed source
  assert (Text.isInfixOf original source && renamedSource /= source)
    "receiver binder alpha-rename source fixture changed shape"
  originalFx <- fixture source
  renamedFx <- fixture renamedSource
  assert (fxPayloadReceiver renamedFx == fxPayloadReceiver originalFx)
    "receiver display alpha-renaming changed declaration-rooted binder identity"
  acceptedReplay renamedFx
  wrongProtocolBinderRejects renamedSource

-- A display rename is not authority for rewriting the activated owner
-- ledger: the checked sender identity is declaration-rooted and stable.
senderBinderDisplayRenamePreservesActivationBoundary :: Text -> Either String ()
senderBinderDisplayRenamePreservesActivationBoundary source = do
  let oldParameter = "endpoint : Client[OwnedPing], payload : Bytes[8]"
      newParameter = "endpoint : Client[OwnedPing], cargo : Bytes[8]"
      oldSend = "let done = send payload on endpoint;"
      newSend = "let done = send cargo on endpoint;"
      oldArchitecture = "bind client.payload = payload;"
      newArchitecture = "bind client.cargo = payload;"
      changed = Text.replace oldArchitecture newArchitecture
        (Text.replace oldSend newSend
          (Text.replace oldParameter newParameter source))
  assert (all (`Text.isInfixOf` source)
            [oldParameter, oldSend, oldArchitecture] && changed /= source)
    "sender parameter rename did not match complete-source fixture"
  originalFx <- fixture source
  renamedFx <- fixture changed
  assert (fxPayloadOwner renamedFx == fxPayloadOwner originalFx
       && fxPayloadReceiver renamedFx == fxPayloadReceiver originalFx
       && fxPayloadOwner renamedFx /= Name "cargo")
    "sender display rename changed declaration-rooted semantic owner"
  acceptedReplay renamedFx
  let before = fxBefore renamedFx
      forged = before { communicationRestrictedOwners =
        Map.insert payloadOccurrence (fxClientProcess renamedFx, Name "cargo")
          (communicationRestrictedOwners before) }
  case checked renamedFx (fxSender renamedFx) (fxReceiver renamedFx) forged of
    Left (RestrictedSourceCoreError
      (RestrictedMessageOwnerMismatch occurrence expectedProcess
        expectedName actualProcess actualName)) ->
        assert (occurrence == payloadOccurrence
             && expectedProcess == fxClientProcess renamedFx
             && expectedName == fxPayloadOwner renamedFx
             && actualProcess == fxClientProcess renamedFx
             && actualName == Name "cargo")
          "forged activation owner lost exact Core diagnostic"
    other -> Left ("forged sender display owner was admitted: " <> show other)


-- Independent component scopes can share a display spelling without sharing
-- declaration-rooted semantic identity or external transfer authority.
dualBinderDisplayCollisionKeepsAuthorityDisjoint :: Text -> Either String ()
dualBinderDisplayCollisionKeepsAuthorityDisjoint source = do
  let senderOld = "endpoint : Client[OwnedPing], payload : Bytes[8]"
      senderNew = "endpoint : Client[OwnedPing], cargo : Bytes[8]"
      sendOld = "let done = send payload on endpoint;"
      sendNew = "let done = send cargo on endpoint;"
      bindOld = "bind client.payload = payload;"
      bindNew = "bind client.cargo = payload;"
      receiverOld = "let (done, received) = receive Bytes[8] on endpoint;"
      receiverNew = "let (done, cargo) = receive Bytes[8] on endpoint;"
      changed = Text.replace receiverOld receiverNew $
        Text.replace bindOld bindNew $
        Text.replace sendOld sendNew $
        Text.replace senderOld senderNew source
  assert (all (\s -> Text.isInfixOf s source)
            [senderOld, sendOld, bindOld, receiverOld]
       && changed /= source
       && Text.isInfixOf receiverNew changed
       && Text.isInfixOf senderNew changed)
    "joint source display collision did not change both scoped declarations"
  original <- fixture source
  fx <- fixture changed
  assert (fxPayloadOwner fx == fxPayloadOwner original
       && fxPayloadReceiver fx == fxPayloadReceiver original
       && fxPayloadOwner fx /= fxPayloadReceiver fx
       && fxPayloadOwner fx /= Name "cargo"
       && fxPayloadReceiver fx /= Name "cargo")
    "colliding display names unexpectedly merged independent semantic binders"
  acceptedReplay fx
  -- A sender's ACTUAL semantic owner is not the externally authorized
  -- receiver binder merely because both source spellings are cargo.
  wrongProtocol <- fixtureWithMessageBinder (Just (fxPayloadOwner fx)) changed
  case checked wrongProtocol (fxSender wrongProtocol) (fxReceiver wrongProtocol)
      (fxBefore wrongProtocol) of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverBinderMismatch expected actual)) ->
        assert (expected == fxPayloadOwner fx
             && actual == fxPayloadReceiver fx)
          "sender identity forged as protocol receiver lost exact mismatch"
    other -> Left ("cross-scoped sender as receiver was admitted: " <> show other)
  -- Likewise a receiver semantic binder is not an activated sender owner.
  let before = fxBefore fx
      forged = before { communicationRestrictedOwners =
        Map.insert payloadOccurrence (fxClientProcess fx, fxPayloadReceiver fx)
          (communicationRestrictedOwners before) }
  case checked fx (fxSender fx) (fxReceiver fx) forged of
    Left (RestrictedSourceCoreError
      (RestrictedMessageOwnerMismatch occurrence expectedProcess
        expectedName actualProcess actualName)) ->
        assert (occurrence == payloadOccurrence
             && expectedProcess == fxClientProcess fx
             && expectedName == fxPayloadOwner fx
             && actualProcess == fxClientProcess fx
             && actualName == fxPayloadReceiver fx)
          "receiver identity forged as activation owner lost exact mismatch"
    other -> Left ("cross-scoped receiver as sender was admitted: " <> show other)
  -- This is independently a rejected *source*, not a forged external
  -- admission or an unresolved proof obligation.
  let validPrefix = "let done = send cargo on endpoint;\n  close done;"
      stalePrefix = "let done = send cargo on endpoint;\n  close endpoint;"
      stale = Text.replace validPrefix stalePrefix changed
  assert (Text.isInfixOf validPrefix changed && stale /= changed)
    "jointly renamed source stale-close negative failed to isolate one edit"
  (_, rejectedSender, _) <- parseParts stale
  case checked fx rejectedSender (fxReceiver fx) (fxBefore fx) of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("joint-display stale-close source lost exact error: " <> show other)


-- FSEM-02: diagnostic priority is observable when *independent* protocol
-- binder and activation owner evidence are both forged. This checks
-- production source validation -> activation owner -> protocol binder
-- ordering; it does not derive any of those authorities from source.
dualAuthorityErrorPriority :: Text -> Either String ()
dualAuthorityErrorPriority source = do
  let forgedProtocolBinder = Name "value"
  fx <- fixtureWithMessageBinder (Just forgedProtocolBinder) source
  let before = fxBefore fx
      forged = before { communicationRestrictedOwners =
        Map.insert payloadOccurrence (fxClientProcess fx, fxPayloadReceiver fx)
          (communicationRestrictedOwners before) }
  -- The owner's exact occurrence/process/semantic name fails before
  -- Core's independently invalid receive-message protocol binder.
  case checked fx (fxSender fx) (fxReceiver fx) forged of
    Left (RestrictedSourceCoreError
      (RestrictedMessageOwnerMismatch occurrence expectedProcess
        expectedName actualProcess actualName)) ->
      assert (occurrence == payloadOccurrence
           && expectedProcess == fxClientProcess fx
           && expectedName == fxPayloadOwner fx
           && actualProcess == fxClientProcess fx
           && actualName == fxPayloadReceiver fx)
        "simultaneous authority faults did not prioritize exact owner mismatch"
    other -> Left ("both forged authorities lost sender-first error: " <> show other)
  -- Repair only the owner evidence; protocol binder mismatch must become
  -- the next precise refusal, without manufacturing an intermediate state.
  case checked fx (fxSender fx) (fxReceiver fx) before of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverBinderMismatch expected actual)) ->
      assert (expected == forgedProtocolBinder
           && actual == fxPayloadReceiver fx)
        "repair of activation owner did not expose protocol-binder error"
    other -> Left ("unrepaired protocol binder was admitted: " <> show other)
  -- The admitted source and both independently matched authorities do
  -- produce the original exact owner/endpoint/spectator transition.
  authorized <- fixture source
  acceptedReplay authorized
  -- A single source Close operand error precedes both external authority
  -- errors, and remains a source-invalid verdict, not an owner/protocol one.
  let good = "let done = send payload on endpoint;\n  close done;"
      bad = "let done = send payload on endpoint;\n  close endpoint;"
      stale = Text.replace good bad source
  assert (Text.isInfixOf good source && stale /= source)
    "priority source negative did not isolate its one edited operand"
  (_, rejectedSender, _) <- parseParts stale
  case checked fx rejectedSender (fxReceiver fx) forged of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("source stale Close did not preempt authority errors: " <> show other)
  -- A source-written receiver type error is likewise prior to the native
  -- owner/protocol gates even while both independent authorities are forged.
  let wrongType = Text.replace "receive Bytes[8] on endpoint"
        "receive U8 on endpoint" source
  assert (wrongType /= source) "priority receiver source type negative not formed"
  (_, _, rejectedReceiver) <- parseParts wrongType
  case checked fx (fxSender fx) rejectedReceiver forged of
    Left (RestrictedSourceMessageTypeMismatch expected actual) ->
      assert (expected == payloadTy && actual == TyUInt 8)
        "source receiver type error lost exact checked types"
    other -> Left ("source receiver type error did not preempt owner gate: " <> show other)


-- The restricted production transfer checks its exact activation owner before
-- any endpoint head, checks sender then receiver head/resource agreement, and
-- checks the independently authorized protocol message binder only after
-- both session steps. Repairing one defect cannot silently admit the next.
-- This diagnostic ordering is specifically for this source fixture.
projectedHeadBinderPriority :: Text -> Either String ()
projectedHeadBinderPriority source = do
  let forgedBinder = Name "value"
  fx <- fixtureWithMessageBinder (Just forgedBinder) source
  let before = fxBefore fx
  sender <- requireProtocol (fxClientProcess fx) before
  receiver <- requireProtocol (fxServerProcess fx) before
  senderBinding <- maybe (Left "priority sender endpoint metadata absent") Right $
    Map.lookup (fxClientOld fx) (protocolEndpoints sender)
  receiverBinding <- maybe (Left "priority receiver endpoint metadata absent") Right $
    Map.lookup (fxServerOld fx) (protocolEndpoints receiver)
  let malformedSender = sender { protocolEndpoints =
        Map.insert (fxClientOld fx)
          (senderBinding { protocolEndpointSession = End doneOutcome })
          (protocolEndpoints sender) }
      malformedReceiver = receiver { protocolEndpoints =
        Map.insert (fxServerOld fx)
          (receiverBinding { protocolEndpointSession = End doneOutcome })
          (protocolEndpoints receiver) }
      originalContexts = communicationProtocolContexts before
      wrongBoth = before { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) malformedSender $
          Map.insert (fxServerProcess fx) malformedReceiver originalContexts }
      wrongReceiver = before { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) malformedReceiver originalContexts }
      ownerAndHeads = wrongBoth { communicationRestrictedOwners =
        Map.insert payloadOccurrence (fxClientProcess fx, fxPayloadReceiver fx)
          (communicationRestrictedOwners wrongBoth) }
  assert (protocolEndpointSession senderBinding /= End doneOutcome
       && protocolEndpointSession receiverBinding /= End doneOutcome)
    "priority negative was already at a terminal session head"
  -- All four independent faults coexist. Sender activation owner refusal wins.
  case checked fx (fxSender fx) (fxReceiver fx) ownerAndHeads of
    Left (RestrictedSourceCoreError
      (RestrictedMessageOwnerMismatch occurrence expectedProcess
        expectedName actualProcess actualName)) ->
      assert (occurrence == payloadOccurrence
           && expectedProcess == fxClientProcess fx
           && expectedName == fxPayloadOwner fx
           && actualProcess == fxClientProcess fx
           && actualName == fxPayloadReceiver fx)
        "owner/head/binder priority lost exact sender-owner rejection"
    other -> Left ("joint owner/head/binder faults missed owner gate: " <> show other)
  -- Only owner repaired: the sender's metadata/session mismatch is first.
  case checked fx (fxSender fx) (fxReceiver fx) wrongBoth of
    Left (RestrictedSourceCoreError
      (RendezvousProtocolError process
        (ProtocolEndpointSessionMismatch endpoint expected actual))) ->
      assert (process == fxClientProcess fx
           && endpoint == fxClientOld fx
           && expected == End doneOutcome
           && actual == protocolEndpointSession senderBinding)
        "sender projected head refusal lost exact context and session evidence"
    other -> Left ("sender projected head fault was not first: " <> show other)
  -- Sender head repaired only: receiver head must still refuse before binder.
  case checked fx (fxSender fx) (fxReceiver fx) wrongReceiver of
    Left (RestrictedSourceCoreError
      (RendezvousProtocolError process
        (ProtocolEndpointSessionMismatch endpoint expected actual))) ->
      assert (process == fxServerProcess fx
           && endpoint == fxServerOld fx
           && expected == End doneOutcome
           && actual == protocolEndpointSession receiverBinding)
        "receiver projected head refusal lost exact context and session evidence"
    other -> Left ("receiver projected head fault was not second: " <> show other)
  -- Both heads repaired: only the independently wrong protocol binder remains.
  case checked fx (fxSender fx) (fxReceiver fx) before of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverBinderMismatch expected actual)) ->
      assert (expected == forgedBinder && actual == fxPayloadReceiver fx)
        "wrong authorized binder did not survive both head repairs"
    other -> Left ("unrepaired message binder was admitted: " <> show other)
  -- Repair the external protocol authorization separately: real source/Core
  -- progression succeeds and the exact owners, endpoints and affine frame hold.
  authorized <- fixture source
  acceptedReplay authorized
  -- One minimally invalid whole-source Close operand must preempt all four
  -- independent environmental faults, not turn into an external-identity error.
  let valid = "let done = send payload on endpoint;\n  close done;"
      invalid = "let done = send payload on endpoint;\n  close endpoint;"
      staleSource = Text.replace valid invalid source
  assert (Text.isInfixOf valid source && staleSource /= source)
    "priority rejected source did not isolate the Close operand edit"
  (_, rejectedSender, _) <- parseParts staleSource
  case checked fx rejectedSender (fxReceiver fx) ownerAndHeads of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("invalid source lost Close error before external faults: " <> show other)

-- FSEM-02: message-binder authority is checked before native resource
-- consumption. A corrupted sender payload map and duplicate receiver slot
-- are independent hostile state faults, not valid activation evidence.
-- Every refusal is a Left with no partial successor; only separate repair of
-- binder, sender payload and receiver slot admits the real transfer.
binderResourceAtomicityPriority :: Text -> Either String ()
binderResourceAtomicityPriority source = do
  forged <- fixtureWithMessageBinder (Just (Name "value")) source
  authorized <- fixture source
  forgedBoth <- corruptBoth forged
  goodBinderBoth <- corruptBoth authorized
  goodBinderReceiverOnly <- corruptReceiver authorized
  assert (fxPayloadReceiver forged /= Name "value")
    "forged external protocol binder unexpectedly matched source receiver"
  -- The receiver message's independently authorized binder is checked before
  -- either resource-map defect, even though both are present simultaneously.
  case checked forged (fxSender forged) (fxReceiver forged) forgedBoth of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverBinderMismatch expected actual)) ->
      assert (expected == Name "value" && actual == fxPayloadReceiver forged)
        "wrong protocol binder lost precedence over both resource faults"
    other -> Left ("forged binder/resource three-fault input admitted: " <> show other)
  -- Repairing ONLY external message authority exposes missing actual sender
  -- linear payload even though its separately activated owner index is intact.
  case checked authorized (fxSender authorized) (fxReceiver authorized)
      goodBinderBoth of
    Left (RestrictedSourceCoreError
      (RestrictedMessageSenderResourceError process (UnknownBinding name))) ->
      assert (process == fxClientProcess authorized
           && name == fxPayloadOwner authorized)
        "missing sender resource lost exact process and binder identity"
    other -> Left ("missing sender resource admitted after binder repair: " <> show other)
  -- Restoring that sender linear payload alone exposes the receiver's
  -- already occupied target slot, not a spurious partial transfer.
  case checked authorized (fxSender authorized) (fxReceiver authorized)
      goodBinderReceiverOnly of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
      assert (process == fxServerProcess authorized
           && name == fxPayloadReceiver authorized)
        "occupied receiver slot lost exact resource error identity"
    other -> Left ("duplicate receiver slot admitted after sender repair: " <> show other)
  -- Pure rejection must be replayable; the hostile input is not consumed.
  assert (checked authorized (fxSender authorized) (fxReceiver authorized)
            goodBinderBoth
       == checked authorized (fxSender authorized) (fxReceiver authorized)
            goodBinderBoth)
    "rejected original resource state was not replay deterministic"
  -- All independently repaired: exact source-derived successor, linear owner
  -- movement and borrowed spectator preservation are checked as before.
  acceptedReplay authorized
  -- A minimally bad complete source Close operand rejects before all three
  -- separately forged authority/resource faults.
  let original = "let done = send payload on endpoint;\n  close done;"
      modified = "let done = send payload on endpoint;\n  close endpoint;"
      rejected = Text.replace original modified source
  assert (Text.isInfixOf original source && rejected /= source)
    "resource priority invalid whole-source witness did not isolate Close edit"
  (_, rejectedSender, _) <- parseParts rejected
  case checked forged rejectedSender (fxReceiver forged) forgedBoth of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("malformed source did not preempt external resource faults: " <> show other)
  where
    corruptReceiver fx = do
      let state = fxBefore fx
      receiver <- requireProtocol (fxServerProcess fx) state
      duplicated <- mapLeft show $ insertBinding Linear
        (fxPayloadReceiver fx) payloadTy (protocolResources receiver)
      let changed = receiver { protocolResources = duplicated }
      Right state { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) changed
          (communicationProtocolContexts state) }

    corruptBoth fx = do
      receiverBad <- corruptReceiver fx
      sender <- requireProtocol (fxClientProcess fx) receiverBad
      let resource = protocolResources sender
          withoutPayload = resource { linearBindings =
            Map.delete (fxPayloadOwner fx) (linearBindings resource) }
          changed = sender { protocolResources = withoutPayload }
      Right receiverBad { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) changed
          (communicationProtocolContexts receiverBad) }


-- FSEM-02: a present but incorrectly typed sender linear binding must be
-- rejected *after* independently admitted protocol/message authority and
-- *before* any receiver-slot insertion. Owner occurrence and endpoint heads
-- remain unchanged. The hostile resource map is not a valid activation.
senderResourceTypeBeforeReceiverSlot :: Text -> Either String ()
senderResourceTypeBeforeReceiverSlot source = do
  fx <- fixture source
  let original = fxBefore fx
  sender <- requireProtocol (fxClientProcess fx) original
  receiver <- requireProtocol (fxServerProcess fx) original
  duplicate <- mapLeft show $ insertBinding Linear
    (fxPayloadReceiver fx) payloadTy (protocolResources receiver)
  let senderResources = protocolResources sender
      badSenderResources = senderResources { linearBindings =
        Map.insert (fxPayloadOwner fx) (TyUInt 8)
          (linearBindings senderResources) }
      badSender = sender { protocolResources = badSenderResources }
      occupiedReceiver = receiver { protocolResources = duplicate }
      contexts = communicationProtocolContexts original
      onlyBadSender = original { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) badSender contexts }
      onlyOccupiedReceiver = original { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) occupiedReceiver contexts }
      both = original { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) badSender $
          Map.insert (fxServerProcess fx) occupiedReceiver contexts }
      replay state = checked fx (fxSender fx) (fxReceiver fx) state
  -- The protocol-message boundary still authorizes Bytes[8], but a forged
  -- native resource holds U8. A receiver collision must not mask this error.
  case replay both of
    Left (RestrictedSourceCoreError
      (RestrictedMessageTransferTypeMismatch expected actual)) ->
        assert (expected == payloadTy && actual == TyUInt 8)
          "wrong sender type lost the exact checked payload mismatch"
    other -> Left ("wrong sender type and receiver collision admitted: " <> show other)
  case replay onlyBadSender of
    Left (RestrictedSourceCoreError
      (RestrictedMessageTransferTypeMismatch expected actual)) ->
        assert (expected == payloadTy && actual == TyUInt 8)
          "receiver repair incorrectly removed sender type refusal"
    other -> Left ("wrong sender type survived receiver repair: " <> show other)
  -- Repairing ONLY the sender's actual resource type reveals the distinct
  -- receiver collision, without changing the external message authority.
  case replay onlyOccupiedReceiver of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
        assert (process == fxServerProcess fx && name == fxPayloadReceiver fx)
          "receiver collision lost its exact process/binder after type repair"
    other -> Left ("receiver collision admitted after sender type repair: " <> show other)
  assert (replay both == replay both)
    "typed sender rejection unexpectedly changed the supplied hostile state"
  -- A separate wholly valid source/state still transfers exact owners and
  -- endpoint successors; resource repairs do not manufacture authority.
  acceptedReplay fx
  let valid = "let done = send payload on endpoint;\n  close done;"
      invalid = "let done = send payload on endpoint;\n  close endpoint;"
      badSource = Text.replace valid invalid source
  assert (Text.isInfixOf valid source && badSource /= source)
    "source negative did not isolate the single Close operand"
  (_, rejectedSender, _) <- parseParts badSource
  case checked fx rejectedSender (fxReceiver fx) both of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("invalid whole source lost priority over resource faults: " <> show other)


-- FSEM-02 NON-NORMATIVE: the receiving name is globally exclusive across all
-- three structural resource maps, not merely within the incoming Linear map.
-- This probes a pre-existing Affine or Unrestricted receiver name even though
-- its linear slot is empty. Deliberately corrupted states are not activations.
crossModeReceiverNameCollision :: Text -> Either String ()
crossModeReceiverNameCollision source = do
  fx <- fixture source
  sequence_ [checkMode fx Affine, checkMode fx Unrestricted]
  acceptedReplay fx
  where
    checkMode :: Fixture -> Mode -> Either String ()
    checkMode fx mode = do
      let original = fxBefore fx
          contexts = communicationProtocolContexts original
          receiverName = fxPayloadReceiver fx
      sender <- requireProtocol (fxClientProcess fx) original
      receiver <- requireProtocol (fxServerProcess fx) original
      occupied <- mapLeft show $ insertBinding mode receiverName TyBool
        (protocolResources receiver)
      assert (Map.notMember receiverName (linearBindings occupied))
        "cross-mode fixture unexpectedly occupied its linear destination"
      case mode of
        Affine -> assert (Map.lookup receiverName (affineBindings occupied) == Just TyBool)
          "affine receiver collision is missing"
        Unrestricted -> assert (Map.lookup receiverName (unrestrictedBindings occupied) == Just TyBool)
          "unrestricted receiver collision is missing"
        Linear -> Left "cross-mode witness cannot use a linear receiver collision"
      let senderResources = protocolResources sender
          badResources = senderResources { linearBindings =
            Map.insert (fxPayloadOwner fx) (TyUInt 8)
              (linearBindings senderResources) }
          badSender = sender { protocolResources = badResources }
          busyReceiver = receiver { protocolResources = occupied }
          onlyBadSender = original { communicationProtocolContexts =
            Map.insert (fxClientProcess fx) badSender contexts }
          onlyBusyReceiver = original { communicationProtocolContexts =
            Map.insert (fxServerProcess fx) busyReceiver contexts }
          both = original { communicationProtocolContexts =
            Map.insert (fxClientProcess fx) badSender $
              Map.insert (fxServerProcess fx) busyReceiver contexts }
          replay state = checked fx (fxSender fx) (fxReceiver fx) state
      -- Actual sender type is checked before attempting ANY mode of receiver
      -- insertion, even though the duplicate name is absent from Linear.
      case replay both of
        Left (RestrictedSourceCoreError
          (RestrictedMessageTransferTypeMismatch expected actual)) ->
            assert (expected == payloadTy && actual == TyUInt 8)
              "cross-mode hostile state lost exact sender type mismatch"
        other -> Left ("cross-mode double fault admitted: " <> show (mode, other))
      case replay onlyBadSender of
        Left (RestrictedSourceCoreError
          (RestrictedMessageTransferTypeMismatch expected actual)) ->
            assert (expected == payloadTy && actual == TyUInt 8)
              "repairing receiver unexpectedly changed sender type error"
        other -> Left ("sender type error lost on receiver repair: " <> show (mode, other))
      -- Repair only sender, leaving a same-name Affine/Unrestricted resource.
      -- insertBinding must refuse the Linear transfer with exact provenance.
      case replay onlyBusyReceiver of
        Left (RestrictedSourceCoreError
          (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
            assert (process == fxServerProcess fx && name == receiverName)
              "cross-mode collision lost exact receiver process and binder"
        other -> Left ("nonlinear same-name receiver was admitted: " <> show (mode, other))
      assert (replay both == replay both)
        "cross-mode hostile replay was nondeterministic"
      -- A minimally rejected whole-source Close operand still wins before
      -- either external resource fault, with the original complete program.
      let valid = "let done = send payload on endpoint;\n  close done;"
          invalid = "let done = send payload on endpoint;\n  close endpoint;"
          badSource = Text.replace valid invalid source
      assert (Text.isInfixOf valid source && badSource /= source)
        "cross-mode source negative did not change the exact Close operand"
      (_, rejectedSender, _) <- parseParts badSource
      case checked fx rejectedSender (fxReceiver fx) both of
        Left (RestrictedSourceSendError
          (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
        other -> Left ("cross-mode faulty source error was masked: " <> show (mode, other))


-- FSEM-02 NON-NORMATIVE: a sender payload with an outstanding shared loan
-- cannot be consumed for ownership transfer. The actual Core consumeLinear
-- checks OwnerBorrowed before receiver insertion, so an independently
-- occupied receiver cannot hide the outstanding loan. Corrupted states here
-- are deliberately not fresh activations; no source grants loan authority.
borrowedSenderTransferRefusal :: Text -> Either String ()
borrowedSenderTransferRefusal source = do
  fx <- fixture source
  let original = fxBefore fx
      contexts = communicationProtocolContexts original
      ownerName = fxPayloadOwner fx
      receiverName = fxPayloadReceiver fx
      replay state = checked fx (fxSender fx) (fxReceiver fx) state
  sender <- requireProtocol (fxClientProcess fx) original
  receiver <- requireProtocol (fxServerProcess fx) original
  loanedResources <- mapLeft show $
    startSharedLoan ownerName (protocolResources sender)
  assert (Set.member ownerName (sharedLoans loanedResources)
       && Map.lookup ownerName (linearBindings loanedResources) == Just payloadTy)
    "borrowed-sender witness changed the owner's type or lost the active loan"
  busyResources <- mapLeft show $
    insertBinding Linear receiverName payloadTy (protocolResources receiver)
  let loanedSender = sender { protocolResources = loanedResources }
      busyReceiver = receiver { protocolResources = busyResources }
      onlyLoaned = original { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) loanedSender contexts }
      onlyBusy = original { communicationProtocolContexts =
        Map.insert (fxServerProcess fx) busyReceiver contexts }
      both = original { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) loanedSender $
          Map.insert (fxServerProcess fx) busyReceiver contexts }
      requiresBorrowed state = case replay state of
        Left (RestrictedSourceCoreError
          (RestrictedMessageSenderResourceError process (OwnerBorrowed name))) ->
            assert (process == fxClientProcess fx && name == ownerName)
              "active sender loan lost its exact process and owner name"
        other -> Left ("borrowed sender was not rejected precisely: " <> show other)
  -- Even a competing receiver insertion fault must not mask the sender loan.
  requiresBorrowed both
  requiresBorrowed onlyLoaned
  assert (replay both == replay both)
    "borrowed sender replay changed its result or produced a partial successor"
  case replay onlyBusy of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
        assert (process == fxServerProcess fx && name == receiverName)
          "ending only the sender loan failed to expose the receiver collision"
    other -> Left ("receiver collision was hidden after loan repair: " <> show other)
  -- Repairing both independently supplied resource states permits only the
  -- already-authorized source transition and exact endpoint/payload frame.
  acceptedReplay fx
  let valid = "let done = send payload on endpoint;\n  close done;"
      invalid = "let done = send payload on endpoint;\n  close endpoint;"
      badSource = Text.replace valid invalid source
  assert (Text.isInfixOf valid source && badSource /= source)
    "borrowed-sender source negative did not isolate one Close operand"
  (_, rejectedSender, _) <- parseParts badSource
  case checked fx rejectedSender (fxReceiver fx) both of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("borrowed-sender resource errors masked source rejection: " <> show other)

-- FSEM-02 NON-NORMATIVE: independently borrowed sender/receiver endpoint
-- predecessors must refuse before a concurrently borrowed sender payload and
-- a busy receiver destination. Explicitly ending each real shared loan
-- reveals the next exact fault, without endpoint or owner-index progression.
-- These hostile resource contexts are NOT certified activations.
borrowedEndpointPrefixPriority :: Text -> Either String ()
borrowedEndpointPrefixPriority source = do
  fx <- fixture source
  let original = fxBefore fx
      contexts = communicationProtocolContexts original
      senderKey = fxClientProcess fx
      receiverKey = fxServerProcess fx
      senderEndpoint = fxClientOld fx
      receiverEndpoint = fxServerOld fx
      payloadOwner = fxPayloadOwner fx
      payloadDestination = fxPayloadReceiver fx
      replay state = checked fx (fxSender fx) (fxReceiver fx) state
  sender <- requireProtocol senderKey original
  receiver <- requireProtocol receiverKey original
  -- Use the actual Context API rather than mutating loan sets by hand.
  senderEndpointLoaned <- mapLeft show $
    startSharedLoan senderEndpoint (protocolResources sender)
  senderBothLoaned <- mapLeft show $
    startSharedLoan payloadOwner senderEndpointLoaned
  receiverEndpointLoaned <- mapLeft show $
    startSharedLoan receiverEndpoint (protocolResources receiver)
  receiverBusy <- mapLeft show $
    insertBinding Linear payloadDestination payloadTy receiverEndpointLoaned
  senderEndpointRepaired <- mapLeft show $
    endSharedLoan senderEndpoint senderBothLoaned
  receiverEndpointRepaired <- mapLeft show $
    endSharedLoan receiverEndpoint receiverBusy
  payloadRepaired <- mapLeft show $
    endSharedLoan payloadOwner senderEndpointRepaired
  let asState senderResources receiverResources =
        original { communicationProtocolContexts =
          Map.insert senderKey (sender { protocolResources = senderResources }) $
            Map.insert receiverKey (receiver { protocolResources = receiverResources })
              contexts }
      allFaults = asState senderBothLoaned receiverBusy
      senderEndpointFixed = asState senderEndpointRepaired receiverBusy
      endpointPairFixed = asState senderEndpointRepaired receiverEndpointRepaired
      allLoansFixed = asState payloadRepaired receiverEndpointRepaired
      allFixed = asState payloadRepaired (protocolResources receiver)
      requiresBorrowedEndpoint expectedProcess expectedName state =
        case replay state of
          Left (RestrictedSourceCoreError
            (RendezvousProtocolError process
              (ProtocolSessionError
                (SessionResourceError (OwnerBorrowed owner))))) ->
              assert (process == expectedProcess && owner == expectedName)
                "endpoint shared loan rejection lost its exact process/name"
          other -> Left ("borrowed endpoint predecessor admitted: " <> show other)
  assert (senderEndpoint /= payloadOwner && senderEndpoint /= receiverEndpoint)
    "endpoint-prefix fixture failed to isolate distinct owners"
  assert (Set.member senderEndpoint (sharedLoans senderBothLoaned)
       && Set.member payloadOwner (sharedLoans senderBothLoaned)
       && Set.member receiverEndpoint (sharedLoans receiverBusy))
    "endpoint-prefix hostile state did not activate all three real loans"
  -- ProtocolSendRequest is checked first; no sender endpoint consumption.
  requiresBorrowedEndpoint senderKey senderEndpoint allFaults
  -- Removing only the sender endpoint loan exposes the receiver's loan.
  requiresBorrowedEndpoint receiverKey receiverEndpoint senderEndpointFixed
  -- Both predecessor loans gone: the sender payload still cannot transfer.
  case replay endpointPairFixed of
    Left (RestrictedSourceCoreError
      (RestrictedMessageSenderResourceError process (OwnerBorrowed name))) ->
        assert (process == senderKey && name == payloadOwner)
          "repairing endpoint loans failed to expose sender payload loan"
    other -> Left ("payload loan priority lost: " <> show other)
  -- All three loans gone: destination collision is now the sole fault.
  case replay allLoansFixed of
    Left (RestrictedSourceCoreError
      (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
        assert (process == receiverKey && name == payloadDestination)
          "repairing all loans failed to expose receiver collision"
    other -> Left ("receiver collision priority lost: " <> show other)
  assert (replay allFaults == replay allFaults
       && replay endpointPairFixed == replay endpointPairFixed)
    "borrowed endpoint trace was not a deterministic pure refusal"
  -- Repairs restore exactly the original checked Core state, not fresh
  -- nominal, protocol, activation, root, or disposal authority.
  assert (allFixed == original && replay allFixed == replay original)
    "all four repairs failed to restore the exact admitted state"
  acceptedReplay fx
  -- The minimally rejected complete source changes only the Close operand.
  let valid = "let done = send payload on endpoint;\n  close done;"
      invalid = "let done = send payload on endpoint;\n  close endpoint;"
      badSource = Text.replace valid invalid source
  assert (Text.isInfixOf valid source && badSource /= source)
    "endpoint-prefix minimally rejected source did not change one operand"
  (_, rejectedSender, _) <- parseParts badSource
  case checked fx rejectedSender (fxReceiver fx) allFaults of
    Left (RestrictedSourceSendError
      (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
    other -> Left ("endpoint resource faults masked source rejection: " <> show other)


-- FSEM-02 NON-NORMATIVE: a receiver destination already owned in Linear or
-- Affine mode may itself have an actual active shared loan. The loan does not
-- hide its cross-map name collision from restricted Linear payload insertion.
-- An independent sender payload loan must be refused *earlier* than this
-- occupied receiver binding. These are intentionally hostile Core states,
-- never fresh source-derived activation or protocol authority.
borrowedOccupiedReceiverCollision :: Text -> Either String ()
borrowedOccupiedReceiverCollision source = do
  fx <- fixture source
  sequence_ [checkMode fx Linear, checkMode fx Affine]
  acceptedReplay fx
  where
    checkMode :: Fixture -> Mode -> Either String ()
    checkMode fx mode = do
      let original = fxBefore fx
          contexts = communicationProtocolContexts original
          senderKey = fxClientProcess fx
          receiverKey = fxServerProcess fx
          senderName = fxPayloadOwner fx
          receiverName = fxPayloadReceiver fx
          replay state = checked fx (fxSender fx) (fxReceiver fx) state
          occupiedType = case mode of
            Linear -> payloadTy
            Affine -> TyBool
            Unrestricted -> TyBool
      sender <- requireProtocol senderKey original
      receiver <- requireProtocol receiverKey original
      occupied <- mapLeft show $
        insertBinding mode receiverName occupiedType (protocolResources receiver)
      receiverLoaned <- mapLeft show $ startSharedLoan receiverName occupied
      receiverLoanEnded <- mapLeft show $ endSharedLoan receiverName receiverLoaned
      senderLoaned <- mapLeft show $
        startSharedLoan senderName (protocolResources sender)
      senderLoanEnded <- mapLeft show $ endSharedLoan senderName senderLoaned
      let asState sr rr = original { communicationProtocolContexts =
            Map.insert senderKey (sender { protocolResources = sr }) $
              Map.insert receiverKey (receiver { protocolResources = rr })
                contexts }
          bothLoaned = asState senderLoaned receiverLoaned
          onlyReceiverLoaned = asState (protocolResources sender) receiverLoaned
          receiverLoanEndedState = asState (protocolResources sender) receiverLoanEnded
          onlySenderLoaned = asState senderLoaned (protocolResources receiver)
          fullyRestored = asState senderLoanEnded (protocolResources receiver)
          expectDuplicate state = case replay state of
            Left (RestrictedSourceCoreError
              (RestrictedMessageReceiverResourceError process (DuplicateBinding name))) ->
                assert (process == receiverKey && name == receiverName)
                  "borrowed occupied receiver lost exact process/binder collision"
            other -> Left ("loaned occupied receiver admitted: " <> show (mode, other))
          expectSenderLoan state = case replay state of
            Left (RestrictedSourceCoreError
              (RestrictedMessageSenderResourceError process (OwnerBorrowed name))) ->
                assert (process == senderKey && name == senderName)
                  "sender loan lost precedence or exact owner provenance"
            other -> Left ("sender/occupied receiver priority lost: " <> show (mode, other))
      assert (Set.member receiverName (sharedLoans receiverLoaned)
           && Set.member senderName (sharedLoans senderLoaned)
           && receiverLoanEnded == occupied
           && senderLoanEnded == protocolResources sender)
        "real shared-loan start/end failed to preserve the occupied resource"
      case mode of
        Affine ->
          assert (Map.lookup receiverName (affineBindings receiverLoaned) == Just TyBool
               && Map.notMember receiverName (linearBindings receiverLoaned))
            "borrowed affine occupancy silently became linear"
        Linear ->
          assert (Map.lookup receiverName (linearBindings receiverLoaned) == Just payloadTy)
            "borrowed linear destination lost its exact checked type"
        Unrestricted -> Left "unrestricted destination cannot start a shared owner loan"
      -- The actual sender's outstanding loan precedes destination insertion.
      expectSenderLoan bothLoaned
      expectSenderLoan onlySenderLoaned
      -- Repairing ONLY sender exposes exact receiver collision even though the
      -- receiver name remains on loan; ending its loan does not unbind it.
      expectDuplicate onlyReceiverLoaned
      expectDuplicate receiverLoanEndedState
      assert (replay onlyReceiverLoaned == replay onlyReceiverLoaned
           && replay bothLoaned == replay bothLoaned)
        "borrowed occupied destination refusal was not deterministic"
      assert (fullyRestored == original && replay fullyRestored == replay original)
        "removing occupied destination and ending both loans altered authority"
      -- The source-level exact rejection must preempt both hostile Core faults.
      let valid = "let done = send payload on endpoint;\n  close done;"
          invalid = "let done = send payload on endpoint;\n  close endpoint;"
          badSource = Text.replace valid invalid source
      assert (Text.isInfixOf valid source && badSource /= source)
        "borrowed occupied receiver source negative did not isolate Close edit"
      (_, rejectedSender, _) <- parseParts badSource
      case checked fx rejectedSender (fxReceiver fx) bothLoaned of
        Left (RestrictedSourceSendError
          (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
        other -> Left ("borrowed occupied Core faults masked source rejection: " <> show (mode, other))

-- FSEM-02 NON-NORMATIVE: source demands a Linear Bytes[8] sender payload.
-- A same-name, same-type Affine or Unrestricted Core sender binding does not
-- satisfy that demand. The real consumeLinear reports WrongStructuralMode
-- before attempting ANY occupied receiver destination; these adversarial
-- resource maps are not validated activations or new protocol authority.
crossModeSenderPayloadRefusal :: Text -> Either String ()
crossModeSenderPayloadRefusal source = do
  fx <- fixture source
  sequence_ [checkModes fx senderMode receiverMode
    | senderMode <- [Affine, Unrestricted]
    , receiverMode <- [Linear, Affine, Unrestricted]]
  acceptedReplay fx
  where
    checkModes :: Fixture -> Mode -> Mode -> Either String ()
    checkModes fx senderMode receiverMode = do
      let original = fxBefore fx
          senderKey = fxClientProcess fx
          receiverKey = fxServerProcess fx
          senderName = fxPayloadOwner fx
          receiverName = fxPayloadReceiver fx
          contexts = communicationProtocolContexts original
          replay state = checked fx (fxSender fx) (fxReceiver fx) state
      sender <- requireProtocol senderKey original
      receiver <- requireProtocol receiverKey original
      let senderResources = protocolResources sender
          receiverResources = protocolResources receiver
          withoutLinearSender = senderResources { linearBindings =
            Map.delete senderName (linearBindings senderResources) }
      assert (Map.lookup senderName (linearBindings senderResources) == Just payloadTy)
        "source-derived sender did not begin with exact linear Bytes[8]"
      wrongModeSender <- mapLeft show $
        insertBinding senderMode senderName payloadTy withoutLinearSender
      restoredSender <- mapLeft show $
        insertBinding Linear senderName payloadTy withoutLinearSender
      busyReceiver <- mapLeft show $
        insertBinding receiverMode receiverName TyBool receiverResources
      assert (restoredSender == senderResources
           && Map.notMember senderName (linearBindings wrongModeSender))
        "same-type sender mode corruption failed to isolate structural mode"
      case senderMode of
        Affine -> assert
          (Map.lookup senderName (affineBindings wrongModeSender) == Just payloadTy)
          "affine sender corruption lost exact Bytes[8] payload"
        Unrestricted -> assert
          (Map.lookup senderName (unrestrictedBindings wrongModeSender) == Just payloadTy)
          "unrestricted sender corruption lost exact Bytes[8] payload"
        Linear -> Left "wrong-mode sender test cannot choose Linear"
      let asState sr rr = original { communicationProtocolContexts =
            Map.insert senderKey (sender { protocolResources = sr }) $
              Map.insert receiverKey (receiver { protocolResources = rr })
                contexts }
          wrongSenderOnly = asState wrongModeSender receiverResources
          receiverBusyOnly = asState senderResources busyReceiver
          both = asState wrongModeSender busyReceiver
          restored = asState restoredSender receiverResources
          expectModeError state = case replay state of
            Left (RestrictedSourceCoreError
              (RestrictedMessageSenderResourceError process
                (WrongStructuralMode name expected actual))) ->
                  assert (process == senderKey && name == senderName
                       && expected == Linear && actual == senderMode)
                    "same-type wrong-mode sender lost exact process/name/mode error"
            other -> Left
              ("wrong-mode sender or receiver collision admitted: " <>
                show (senderMode, receiverMode, other))
          expectDuplicate state = case replay state of
            Left (RestrictedSourceCoreError
              (RestrictedMessageReceiverResourceError process
                (DuplicateBinding name))) ->
                  assert (process == receiverKey && name == receiverName)
                    "wrong-mode repair lost exact occupied receiver diagnostic"
            other -> Left
              ("receiver collision admitted after sender mode repair: " <>
                show (senderMode, receiverMode, other))
      -- Core consumes the typed sender's required *linear* resource before
      -- attempting any receiver insertion, including cross-mode duplicates.
      expectModeError both
      expectModeError wrongSenderOnly
      expectDuplicate receiverBusyOnly
      assert (restored == original && replay restored == replay original
           && replay both == replay both)
        "structural mode repair changed previously authorized replay"
      -- One exact edit to an otherwise accepted complete source rejects
      -- before hostile Core mode/collision faults.
      let valid = "let done = send payload on endpoint;\n  close done;"
          invalid = "let done = send payload on endpoint;\n  close endpoint;"
          badSource = Text.replace valid invalid source
      assert (Text.isInfixOf valid source && badSource /= source)
        "wrong-mode sender source negative did not isolate Close operand"
      (_, badSender, _) <- parseParts badSource
      case checked fx badSender (fxReceiver fx) both of
        Left (RestrictedSourceSendError
          (GrammarV1ComponentSendCloseCloseMismatch _ _)) -> Right ()
        other -> Left
          ("malformed source lost priority over wrong-mode resource: " <>
            show (senderMode, receiverMode, other))

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



-- Distinct from the select/offer diamond: this rechecks a real parsed
-- restricted Bytes[8] send/receive and its ORIGINAL Core predecessor
-- before executing the two possible explicitly authorized End close orders.
sourceCloseDiamondFrom
  :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ProcessCommunicationState -> Outcome -> Outcome
  -> Either GrammarV1RestrictedSourceCloseDiamondError
       GrammarV1RestrictedSourceCloseDiamondTransition
sourceCloseDiamondFrom fx sender receiver before senderOutcome receiverOutcome =
  grammarV1CheckRestrictedSourceCloseDiamond
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx) payloadOccurrence
    (fxNetwork fx) before senderOutcome receiverOutcome

sourceCloseDiamondReplay :: Fixture -> Either String ()
sourceCloseDiamondReplay fx = do
  let run = sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
        (fxBefore fx) doneOutcome doneOutcome
  first <- mapLeft show run
  second <- mapLeft show run
  assert (first == second) "restricted source diamond is nondeterministic"
  let rendezvous = restrictedSourceDiamondRendezvous first
      forward = restrictedSourceDiamondForward first
      ready = restrictedSourceNext rendezvous
      peerFirst = restrictedSourceDiamondReceiverFirst first
      after = restrictedSourceDiamondReverse first
      ownersBefore = communicationRestrictedOwners ready
      ownersPeerFirst = communicationRestrictedOwners peerFirst
      ownersAfter = communicationRestrictedOwners after
      revision = binaryProtocolInstanceRevision (fxInstance fx)
  independentlyChecked <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  independentlyForward <- mapLeft show $
    closeFromSource fx (fxSender fx) (fxReceiver fx)
      independentlyChecked clientRole serverRole doneOutcome doneOutcome
  independentlyPeerFirst <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) ready
      (fxServerProcess fx) (fxServerNext fx) revision serverRole doneOutcome
  independentlyAfter <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) independentlyPeerFirst
      (fxClientProcess fx) (fxClientNext fx) revision clientRole doneOutcome
  assert (rendezvous == independentlyChecked
       && forward == independentlyForward
       && peerFirst == independentlyPeerFirst
       && after == independentlyAfter
       && after == restrictedSourceCloseNext forward)
    "restricted source close diamond did not equal independent full Core replay"
  assert (Map.lookup serverEndpointOccurrence ownersPeerFirst == Nothing
       && Map.lookup clientEndpointOccurrence ownersPeerFirst ==
            Map.lookup clientEndpointOccurrence ownersBefore
       && Map.lookup payloadOccurrence ownersPeerFirst ==
            Just (fxServerProcess fx, fxPayloadReceiver fx)
       && Map.lookup spectatorOccurrence ownersPeerFirst ==
            Map.lookup spectatorOccurrence ownersBefore
       && ownersAfter == Map.delete clientEndpointOccurrence
          (Map.delete serverEndpointOccurrence ownersBefore))
    "restricted diamond modified endpoint/payload/spectator occurrence ledger"
  senderContext <- requireProtocol (fxClientProcess fx) after
  receiverContext <- requireProtocol (fxServerProcess fx) after
  assert (Map.lookup (fxPayloadReceiver fx)
            (linearBindings (protocolResources receiverContext)) == Just payloadTy
       && Map.lookup spectatorName
            (affineBindings (protocolResources senderContext)) == Just TyBool
       && Map.notMember (fxClientNext fx) (protocolEndpoints senderContext)
       && Map.notMember (fxServerNext fx) (protocolEndpoints receiverContext))
    "restricted diamond disposed the payload/spectator or retained End heads"


-- Separately project an end-to-end EXACT finite source-derived owner trace
-- through the new production adapter. No root or payload-disposition authority
-- is inferred from the local source close.
sourceSuccessorTraceFrom
  :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ActivationOccurrenceKey -> ActivationOccurrenceKey
  -> Either GrammarV1RestrictedSourceSuccessorTraceError
       GrammarV1RestrictedSourceSuccessorTrace
sourceSuccessorTraceFrom fx sender receiver senderOccurrence receiverOccurrence =
  grammarV1CheckRestrictedSourceSuccessorTrace
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx)
    senderOccurrence receiverOccurrence payloadOccurrence
    (fxNetwork fx) (fxBefore fx) doneOutcome doneOutcome

sourceSuccessorTraceReplay :: Fixture -> Either String ()
sourceSuccessorTraceReplay fx = do
  trace <- mapLeft show $
    sourceSuccessorTraceFrom fx (fxSender fx) (fxReceiver fx)
      clientEndpointOccurrence serverEndpointOccurrence
  again <- mapLeft show $
    sourceSuccessorTraceFrom fx (fxSender fx) (fxReceiver fx)
      clientEndpointOccurrence serverEndpointOccurrence
  diamond <- mapLeft show $
    sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome
  let before = communicationRestrictedOwners (fxBefore fx)
      next = restrictedSuccessorTraceRendezvousOwners trace
      terminal = restrictedSuccessorTraceTerminalOwners trace
      expectedNext = Map.insert payloadOccurrence
        (fxServerProcess fx, fxPayloadReceiver fx)
        (Map.insert clientEndpointOccurrence
          (fxClientProcess fx, fxClientNext fx)
          (Map.insert serverEndpointOccurrence
            (fxServerProcess fx, fxServerNext fx) before))
  assert (trace == again
       && restrictedSuccessorTraceDiamond trace == diamond
       && next == expectedNext
       && terminal == Map.delete clientEndpointOccurrence
           (Map.delete serverEndpointOccurrence expectedNext)
       && Map.lookup spectatorOccurrence next ==
           Map.lookup spectatorOccurrence before
       && Map.lookup spectatorOccurrence terminal ==
           Map.lookup spectatorOccurrence before
       && Map.lookup payloadOccurrence terminal ==
           Just (fxServerProcess fx, fxPayloadReceiver fx))
    "source-derived successor trace lost predecessor/successor identity, payload or spectator"


-- Restricted Bytes[8] source + original activated Core predecessor are
-- independently rechecked before exposing either one-sided End-prefix state.
-- This is distinct from the choice prefix case: the transferred linear payload
-- MUST survive on the receiver after either endpoint is retired.
sourceClosePrefixFrom
  :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ProcessCommunicationState -> Outcome -> Outcome
  -> Either GrammarV1RestrictedClosePrefixError GrammarV1RestrictedClosePrefixes
sourceClosePrefixFrom fx sender receiver original senderOutcome receiverOutcome =
  grammarV1CheckRestrictedSourceClosePrefixes
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx)
    clientEndpointOccurrence serverEndpointOccurrence payloadOccurrence
    (fxNetwork fx) original senderOutcome receiverOutcome

sourceClosePrefixReplay :: Fixture -> Either String ()
sourceClosePrefixReplay fx = do
  first <- mapLeft show $ sourceClosePrefixFrom fx (fxSender fx) (fxReceiver fx)
    (fxBefore fx) doneOutcome doneOutcome
  again <- mapLeft show $ sourceClosePrefixFrom fx (fxSender fx) (fxReceiver fx)
    (fxBefore fx) doneOutcome doneOutcome
  let trace = restrictedClosePrefixTrace first
      diamond = restrictedSuccessorTraceDiamond trace
      ready = restrictedSourceNext (restrictedSourceDiamondRendezvous diamond)
      senderFirst = restrictedClosePrefixSenderFirst first
      receiverFirst = restrictedClosePrefixReceiverFirst first
      readyOwners = communicationRestrictedOwners ready
      senderOwners = communicationRestrictedOwners senderFirst
      receiverOwners = communicationRestrictedOwners receiverFirst
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      expectedPayload = Just (fxServerProcess fx, fxPayloadReceiver fx)
  independentlySender <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) ready
      (fxClientProcess fx) (fxClientNext fx) revision clientRole doneOutcome
  independentlyReceiver <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) ready
      (fxServerProcess fx) (fxServerNext fx) revision serverRole doneOutcome
  assert (first == again
       && senderFirst == independentlySender
       && receiverFirst == independentlyReceiver
       && receiverFirst == restrictedSourceDiamondReceiverFirst diamond
       && senderOwners == Map.delete clientEndpointOccurrence readyOwners
       && receiverOwners == Map.delete serverEndpointOccurrence readyOwners
       && Map.lookup clientEndpointOccurrence senderOwners == Nothing
       && Map.lookup serverEndpointOccurrence receiverOwners == Nothing
       && Map.lookup serverEndpointOccurrence senderOwners ==
           Just (fxServerProcess fx, fxServerNext fx)
       && Map.lookup clientEndpointOccurrence receiverOwners ==
           Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup payloadOccurrence senderOwners == expectedPayload
       && Map.lookup payloadOccurrence receiverOwners == expectedPayload
       && Map.lookup spectatorOccurrence senderOwners ==
           Map.lookup spectatorOccurrence readyOwners
       && Map.lookup spectatorOccurrence receiverOwners ==
           Map.lookup spectatorOccurrence readyOwners
       && restrictedSourceDiamondReverse diamond ==
           restrictedSourceCloseNext (restrictedSourceDiamondForward diamond))
    "restricted one-sided close prefix changed payload, spectators, live peer or final equality"
  senderContext <- requireProtocol (fxClientProcess fx) senderFirst
  receiverContext <- requireProtocol (fxServerProcess fx) receiverFirst
  assert (Map.lookup spectatorName
            (affineBindings (protocolResources senderContext)) == Just TyBool
       && Map.lookup (fxPayloadReceiver fx)
            (linearBindings (protocolResources receiverContext)) == Just payloadTy)
    "one-sided Core close disposed a nonendpoint resource"

sourceClosePrefixRejectedSource :: Fixture -> Text -> Either String ()
sourceClosePrefixRejectedSource fx rejected = do
  (_, badSender, _) <- parseParts rejected
  case sourceClosePrefixFrom fx badSender (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome of
    Left (RestrictedClosePrefixSourceError
      (RestrictedSuccessorTraceDiamondError
        (RestrictedSourceCloseDiamondRendezvousError
          (RestrictedSourceSendError
            (GrammarV1ComponentSendCloseCloseMismatch _ _))))) -> Right ()
    other -> Left ("rejected source acquired a close prefix: " <> show other)

sourceClosePrefixStalePredecessor :: Fixture -> Either String ()
sourceClosePrefixStalePredecessor fx = do
  rendezvous <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case sourceClosePrefixFrom fx (fxSender fx) (fxReceiver fx)
      (restrictedSourceNext rendezvous) doneOutcome doneOutcome of
    Left (RestrictedClosePrefixSourceError
      (RestrictedSuccessorTraceDiamondError
        (RestrictedSourceCloseDiamondRendezvousError
          (RestrictedSourceCoreError
            (RestrictedMessageOwnerMismatch key _ _ process name))))) ->
      assert (key == payloadOccurrence
           && process == fxServerProcess fx
           && name == fxPayloadReceiver fx)
        "stale prefix predecessor lost exact consumed/received payload identity"
    other -> Left ("stale restricted predecessor acquired a prefix: " <> show other)

sourceClosePrefixWrongOutcome :: Fixture -> Either String ()
sourceClosePrefixWrongOutcome fx = do
  let wrong = Outcome "NotDone"
  case sourceClosePrefixFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome wrong of
    Left (RestrictedClosePrefixSourceError
      (RestrictedSuccessorTraceDiamondError
        (RestrictedSourceCloseDiamondForwardError
          (RestrictedSourceCloseReceiverCoreError
            (EndpointClosureProtocolError process
              (ProtocolSessionError (CloseOutcomeMismatch expected actual))))))) ->
      assert (process == fxServerProcess fx
           && expected == doneOutcome && actual == wrong)
        "wrong peer End outcome lost exact rejection provenance"
    other -> Left ("unauthorized peer End outcome acquired a prefix: " <> show other)

sourceClosePrefixRepeatRetirement :: Fixture -> Either String ()
sourceClosePrefixRepeatRetirement fx = do
  prefix <- mapLeft show $ sourceClosePrefixFrom fx
    (fxSender fx) (fxReceiver fx) (fxBefore fx) doneOutcome doneOutcome
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  case closeProcessEndpointState (fxNetwork fx)
      (restrictedClosePrefixSenderFirst prefix) (fxClientProcess fx)
      (fxClientNext fx) revision clientRole doneOutcome of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxClientProcess fx && endpoint == fxClientNext fx)
        "sender-first stale endpoint rejection lost exact retired identity"
    other -> Left ("sender endpoint was retired twice: " <> show other)
  case closeProcessEndpointState (fxNetwork fx)
      (restrictedClosePrefixReceiverFirst prefix) (fxServerProcess fx)
      (fxServerNext fx) revision serverRole doneOutcome of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxServerProcess fx && endpoint == fxServerNext fx)
        "receiver-first stale endpoint rejection lost exact retired identity"
    other -> Left ("receiver endpoint was retired twice: " <> show other)

-- Alpha-renaming source display spelling without changing declaration-rooted
-- binder ordinal MUST keep the semantic successor and native Core state.
-- This is one checked fixture, not universal alpha-equivalence.
sourceSuccessorTraceAlphaRename :: Fixture -> Text -> Either String ()
sourceSuccessorTraceAlphaRename fx accepted = do
  let changed = Text.replace
        "let done = send payload on endpoint;\n  close done;"
        "let successor = send payload on endpoint;\n  close successor;"
        accepted
  assert (changed /= accepted) "alpha-renaming fixture did not change source"
  (_, renamedSender, _) <- parseParts changed
  checkedSender <- case grammarV1CheckedComponentSendClose senderRoot renamedSender of
    Just (Right result) -> Right result
    other -> Left ("renamed source no longer checks: " <> show other)
  assert (grammarV1ResolvedBinderDisplayName
            (checkedComponentSendSuccessor checkedSender) == "successor"
       && grammarV1ResolvedBinderCoreName
            (checkedComponentSendSuccessor checkedSender) == fxClientNext fx)
    "alpha-renamed successor changed its declaration-rooted semantic identity"
  renamedTrace <- mapLeft show $
    sourceSuccessorTraceFrom fx renamedSender (fxReceiver fx)
      clientEndpointOccurrence serverEndpointOccurrence
  originalTrace <- mapLeft show $
    sourceSuccessorTraceFrom fx (fxSender fx) (fxReceiver fx)
      clientEndpointOccurrence serverEndpointOccurrence
  assert (restrictedSuccessorTraceRendezvousOwners renamedTrace ==
            restrictedSuccessorTraceRendezvousOwners originalTrace
       && restrictedSuccessorTraceTerminalOwners renamedTrace ==
            restrictedSuccessorTraceTerminalOwners originalTrace)
    "alpha-renamed source changed native successor/terminal owner trace"

sourceSuccessorTraceRejectedSource :: Fixture -> Text -> Either String ()
sourceSuccessorTraceRejectedSource fx rejected = do
  (_, badSender, _) <- parseParts rejected
  case sourceSuccessorTraceFrom fx badSender (fxReceiver fx)
      clientEndpointOccurrence serverEndpointOccurrence of
    Left (RestrictedSuccessorTraceDiamondError
      (RestrictedSourceCloseDiamondRendezvousError
        (RestrictedSourceSendError
          (GrammarV1ComponentSendCloseCloseMismatch _ _)))) -> Right ()
    other -> Left ("minimally rejected source acquired a successor trace: " <> show other)

sourceSuccessorTraceWrongOccurrence :: Fixture -> Either String ()
sourceSuccessorTraceWrongOccurrence fx =
  let unexpectedOccurrence = ActivationOccurrenceKey "fsem02.external.foreign.endpoint"
  in case sourceSuccessorTraceFrom fx (fxSender fx) (fxReceiver fx)
      unexpectedOccurrence serverEndpointOccurrence of
    Left (RestrictedSuccessorTracePredecessorMismatch
      occurrence expected Nothing) ->
        assert (occurrence == unexpectedOccurrence
             && expected == (fxClientProcess fx, fxClientOld fx))
          "foreign occurrence rejection lost exact checked source predecessor"
    other -> Left ("invented external endpoint occurrence entered successor trace: " <> show other)

sourceSuccessorTraceAliasedOccurrence :: Fixture -> Either String ()
sourceSuccessorTraceAliasedOccurrence fx =
  case sourceSuccessorTraceFrom fx (fxSender fx) (fxReceiver fx)
      payloadOccurrence serverEndpointOccurrence of
    Left RestrictedSuccessorTraceAliasedOccurrence -> Right ()
    other -> Left ("aliased payload and endpoint occurrence entered trace: " <> show other)

sourceCloseDiamondRejectedSource :: Fixture -> Text -> Either String ()
sourceCloseDiamondRejectedSource fx rejected = do
  (_, badSender, _) <- parseParts rejected
  case sourceCloseDiamondFrom fx badSender (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome of
    Left (RestrictedSourceCloseDiamondRendezvousError
      (RestrictedSourceSendError
        (GrammarV1ComponentSendCloseCloseMismatch _ _))) -> Right ()
    other -> Left ("minimally rejected source entered restricted close diamond: " <> show other)

sourceCloseDiamondStalePredecessor :: Fixture -> Either String ()
sourceCloseDiamondStalePredecessor fx = do
  checkedTransition <- mapLeft show $
    checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
      (restrictedSourceNext checkedTransition) doneOutcome doneOutcome of
    Left (RestrictedSourceCloseDiamondRendezvousError
      (RestrictedSourceCoreError
        (RestrictedMessageOwnerMismatch key _ _ actualProcess actualName))) ->
      assert (key == payloadOccurrence
           && actualProcess == fxServerProcess fx
           && actualName == fxPayloadReceiver fx)
        "stale restricted payload did not retain exact transferred owner"
    other -> Left ("stale predecessor advanced to the close diamond: " <> show other)

sourceCloseDiamondWrongSessionHead :: Fixture -> Either String ()
sourceCloseDiamondWrongSessionHead fx = do
  sender <- requireProtocol (fxClientProcess fx) (fxBefore fx)
  let old = fxClientOld fx
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) clientRole
        (End doneOutcome)
      altered = sender { protocolEndpoints =
        Map.insert old wrong (protocolEndpoints sender) }
      before = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) altered
          (communicationProtocolContexts (fxBefore fx)) }
  case sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
      before doneOutcome doneOutcome of
    Left (RestrictedSourceCloseDiamondRendezvousError
      (RestrictedSourceCoreError (RendezvousProtocolError process _))) ->
      assert (process == fxClientProcess fx)
        "wrong predecessor session head lost exact sending process"
    other -> Left ("wrong session head advanced to restricted close diamond: " <> show other)

sourceCloseDiamondWrongOutcome :: Fixture -> Either String ()
sourceCloseDiamondWrongOutcome fx = do
  let wrong = Outcome "NotDone"
  case sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome wrong of
    Left (RestrictedSourceCloseDiamondForwardError
      (RestrictedSourceCloseReceiverCoreError
        (EndpointClosureProtocolError process
          (ProtocolSessionError (CloseOutcomeMismatch expected actual))))) ->
      assert (process == fxServerProcess fx
           && expected == doneOutcome && actual == wrong)
        "receiver End mismatch lost exact error class"
    other -> Left ("wrong End outcome advanced to restricted close diamond: " <> show other)

sourceCloseDiamondReceiverFirstStale :: Fixture -> Either String ()
sourceCloseDiamondReceiverFirstStale fx = do
  diamond <- mapLeft show $
    sourceCloseDiamondFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome
  case closeProcessEndpointState (fxNetwork fx)
      (restrictedSourceDiamondReceiverFirst diamond)
      (fxServerProcess fx) (fxServerNext fx)
      (binaryProtocolInstanceRevision (fxInstance fx))
      serverRole doneOutcome of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxServerProcess fx && endpoint == fxServerNext fx)
        "receiver-first repeat close lost the retired endpoint identity"
    other -> Left ("receiver-first close allowed stale endpoint reuse: " <> show other)

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
  grammarV1CheckRestrictedSourceTerminal (fxInstance fx)
    (fxNetwork fx) (fxBefore fx) rendezvous closed
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

-- Native endpoint closure may accept a forged affine spectator, but its
-- post-rendezvous context must still be the exact predecessor's successor.
sourceTerminalRejectForgedRendezvousState :: Fixture -> Either String ()
sourceTerminalRejectForgedRendezvousState fx = do
  (rendezvous, _) <- terminalPrefix fx
  let next = restrictedSourceNext rendezvous
  sender <- requireProtocol (fxClientProcess fx) next
  forgedResources <- mapLeft show $ insertBinding Affine
    (Name "forged-post-rendezvous") TyBool (protocolResources sender)
  let altered = sender { protocolResources = forgedResources }
      forgedNext = next { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) altered
          (communicationProtocolContexts next) }
      forgedRendezvous = rendezvous { restrictedSourceNext = forgedNext }
  forgedClose <- mapLeft show $
    closeFromSource fx (fxSender fx) (fxReceiver fx) forgedRendezvous
      clientRole serverRole doneOutcome doneOutcome
  case terminalCheck fx forgedRendezvous forgedClose
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      Map.empty emptyRootResidue of
    Left RestrictedSourceTerminalRendezvousStateMismatch -> Right ()
    other -> Left ("forged post-rendezvous context was accepted: " <> show other)

-- Source success must not reconstruct a missing activation-owned occurrence.
sourceTerminalRejectMissingPredecessorOwner :: Fixture -> Either String ()
sourceTerminalRejectMissingPredecessorOwner fx = do
  (rendezvous, closed) <- terminalPrefix fx
  let original = fxBefore fx
      missing = original { communicationRestrictedOwners =
        Map.delete payloadOccurrence (communicationRestrictedOwners original) }
  case grammarV1CheckRestrictedSourceTerminal (fxInstance fx)
      (fxNetwork fx) missing rendezvous closed
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      doneOutcome doneOutcome Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalRendezvousReplayError
      (RestrictedMessageOwnerUnknown occurrence)) ->
        assert (occurrence == payloadOccurrence)
          "predecessor replay lost the exact missing occurrence key"
    other -> Left ("missing predecessor payload owner admitted: " <> show other)

-- A purported terminal cached state cannot excuse the original non-Send head.
sourceTerminalRejectWrongPredecessorHead :: Fixture -> Either String ()
sourceTerminalRejectWrongPredecessorHead fx = do
  (rendezvous, closed) <- terminalPrefix fx
  sender <- requireProtocol (fxClientProcess fx) (fxBefore fx)
  let old = fxClientOld fx
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) clientRole
        (End doneOutcome)
      invalidSender = sender { protocolEndpoints =
        Map.insert old wrong (protocolEndpoints sender) }
      invalidBefore = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) invalidSender
          (communicationProtocolContexts (fxBefore fx)) }
  case grammarV1CheckRestrictedSourceTerminal (fxInstance fx)
      (fxNetwork fx) invalidBefore rendezvous closed
      (senderTerminalPlan fx) (receiverTerminalPlan fx)
      doneOutcome doneOutcome Map.empty emptyRootResidue of
    Left (RestrictedSourceTerminalRendezvousReplayError
      (RendezvousProtocolError process _)) ->
        assert (process == fxClientProcess fx)
          "predecessor protocol rejection changed sender identity"
    other -> Left ("wrong original session head admitted: " <> show other)


-- FSEM-02 NON-NORMATIVE: exact production source/terminal-head and resource
-- continuation agreement. The End expectations come from external protocol
-- authority, not the source's spelling of a close operand.
typedHeadFrom
  :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ProcessCommunicationState -> Outcome -> Outcome
  -> Either GrammarV1RestrictedTerminalHeadError GrammarV1RestrictedTerminalHeadTrace
typedHeadFrom fx sender receiver before senderEnd receiverEnd =
  grammarV1CheckRestrictedTerminalHeadTrace
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx) payloadOccurrence
    (fxNetwork fx) before senderEnd receiverEnd


-- The original checked source and activated predecessor are independently
-- replayed by both production adapters. The second adapter checks all owner
-- occurrences at each first-End prefix, including restricted payload/frame.
typedPrefixFrom
  :: Fixture -> GrammarV1ComponentDecl -> GrammarV1ComponentDecl
  -> ProcessCommunicationState -> Outcome -> Outcome
  -> Either GrammarV1RestrictedTypedPrefixError GrammarV1RestrictedTypedPrefixTrace
typedPrefixFrom fx sender receiver before senderEnd receiverEnd =
  grammarV1CheckRestrictedTypedPrefixTrace
    emptyStaticContext senderRoot sender receiverRoot receiver
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx)
    clientEndpointOccurrence serverEndpointOccurrence payloadOccurrence
    (fxNetwork fx) before senderEnd receiverEnd

typedPrefixAccepted :: Fixture -> Either String ()
typedPrefixAccepted fx = do
  first <- mapLeft show $ typedPrefixFrom fx (fxSender fx) (fxReceiver fx)
    (fxBefore fx) doneOutcome doneOutcome
  second <- mapLeft show $ typedPrefixFrom fx (fxSender fx) (fxReceiver fx)
    (fxBefore fx) doneOutcome doneOutcome
  separateHeads <- mapLeft show $ typedHeadFrom fx (fxSender fx) (fxReceiver fx)
    (fxBefore fx) doneOutcome doneOutcome
  separatePrefixes <- mapLeft show $ sourceClosePrefixFrom fx (fxSender fx)
    (fxReceiver fx) (fxBefore fx) doneOutcome doneOutcome
  let prefixes = restrictedTypedPrefixOwners first
      headResult = restrictedTypedPrefixHeads first
      ready = restrictedSourceNext (restrictedTerminalHeadSourceStep headResult)
      senderOwners = communicationRestrictedOwners
        (restrictedClosePrefixSenderFirst prefixes)
      receiverOwners = communicationRestrictedOwners
        (restrictedClosePrefixReceiverFirst prefixes)
      expectedPayload = Just (fxServerProcess fx, fxPayloadReceiver fx)
  assert (first == second
       && headResult == separateHeads
       && prefixes == separatePrefixes
       && Map.lookup payloadOccurrence senderOwners == expectedPayload
       && Map.lookup payloadOccurrence receiverOwners == expectedPayload
       && Map.lookup spectatorOccurrence senderOwners ==
            Map.lookup spectatorOccurrence (communicationRestrictedOwners ready)
       && Map.lookup spectatorOccurrence receiverOwners ==
            Map.lookup spectatorOccurrence (communicationRestrictedOwners ready))
    "typed End-prefix composition changed replay, transferred payload or spectator"

typedPrefixRejectedSource :: Fixture -> Text -> Either String ()
typedPrefixRejectedSource fx rejected = do
  (_, badSender, _) <- parseParts rejected
  case typedPrefixFrom fx badSender (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome of
    Left (RestrictedTypedPrefixHeadError
      (RestrictedTerminalHeadSourceError
        (RestrictedSourceSendError
          (GrammarV1ComponentSendCloseCloseMismatch _ _)))) -> Right ()
    other -> Left ("stale-close source acquired typed End prefixes: " <> show other)

typedPrefixWrongOutcome :: Fixture -> Either String ()
typedPrefixWrongOutcome fx =
  case typedPrefixFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome (Outcome "NotDone") of
    Left (RestrictedTypedPrefixHeadError
      (RestrictedTerminalHeadOutcomeMismatch process old actual supplied)) ->
      assert (process == fxServerProcess fx && old == fxServerOld fx
           && actual == doneOutcome && supplied == Outcome "NotDone")
        "wrong End outcome lost exact predecessor/process diagnostic"
    other -> Left ("wrong End authority acquired typed prefix: " <> show other)

typedPrefixWrongSessionHead :: Fixture -> Either String ()
typedPrefixWrongSessionHead fx = do
  sender <- requireProtocol (fxClientProcess fx) (fxBefore fx)
  let old = fxClientOld fx
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) clientRole (End doneOutcome)
      changed = sender { protocolEndpoints = Map.insert old wrong
        (protocolEndpoints sender) }
      before = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) changed
          (communicationProtocolContexts (fxBefore fx)) }
  case typedPrefixFrom fx (fxSender fx) (fxReceiver fx)
      before doneOutcome doneOutcome of
    Left (RestrictedTypedPrefixHeadError
      (RestrictedTerminalHeadSourceError
        (RestrictedSourceCoreError (RendezvousProtocolError process _)))) ->
      assert (process == fxClientProcess fx)
        "invalid original Send head lost its exact process diagnostic"
    other -> Left ("wrong original session head acquired typed prefix: " <> show other)

typedPrefixStaleOriginal :: Fixture -> Either String ()
typedPrefixStaleOriginal fx = do
  first <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case typedPrefixFrom fx (fxSender fx) (fxReceiver fx)
      (restrictedSourceNext first) doneOutcome doneOutcome of
    Left (RestrictedTypedPrefixHeadError
      (RestrictedTerminalHeadSourceError
        (RestrictedSourceCoreError
          (RestrictedMessageOwnerMismatch key _ _ process name)))) ->
      assert (key == payloadOccurrence && process == fxServerProcess fx
           && name == fxPayloadReceiver fx)
        "stale head lost its transferred occurrence diagnostic"
    other -> Left ("consumed original endpoint acquired typed prefix: " <> show other)

typedPrefixAliasedOccurrence :: Fixture -> Either String ()
typedPrefixAliasedOccurrence fx =
  case grammarV1CheckRestrictedTypedPrefixTrace
    emptyStaticContext senderRoot (fxSender fx) receiverRoot (fxReceiver fx)
    (fxInstance fx) clientRole serverRole
    (fxClientProcess fx) (fxServerProcess fx)
    serverEndpointOccurrence serverEndpointOccurrence payloadOccurrence
    (fxNetwork fx) (fxBefore fx) doneOutcome doneOutcome of
    Left (RestrictedTypedPrefixLedgerError
      (RestrictedClosePrefixSourceError
        RestrictedSuccessorTraceAliasedOccurrence)) -> Right ()
    other -> Left ("aliased endpoint occurrences acquired typed prefix: " <> show other)


typedHeadAccepted :: Fixture -> Either String ()
typedHeadAccepted fx = do
  first <- mapLeft show $
    typedHeadFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome
  second <- mapLeft show $
    typedHeadFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome
  assert (first == second) "terminal head replay is nondeterministic"
  let progressed = restrictedSourceNext (restrictedTerminalHeadSourceStep first)
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      expectedSender = ProtocolEndpointBinding
        (fxClientNext fx) revision clientRole (End doneOutcome)
      expectedReceiver = ProtocolEndpointBinding
        (fxServerNext fx) revision serverRole (End doneOutcome)
  sender <- requireProtocol (fxClientProcess fx) progressed
  receiver <- requireProtocol (fxServerProcess fx) progressed
  assert (restrictedTerminalHeadSenderSuccessor first == expectedSender
       && restrictedTerminalHeadReceiverSuccessor first == expectedReceiver
       && Map.lookup (fxClientNext fx) (protocolEndpoints sender) == Just expectedSender
       && Map.lookup (fxServerNext fx) (protocolEndpoints receiver) == Just expectedReceiver
       && Map.lookup (fxClientNext fx) (linearBindings (protocolResources sender)) ==
            Just (TyEndpoint (End doneOutcome))
       && Map.lookup (fxServerNext fx) (linearBindings (protocolResources receiver)) ==
            Just (TyEndpoint (End doneOutcome))
       && Map.notMember (fxClientOld fx) (protocolEndpoints sender)
       && Map.notMember (fxServerOld fx) (protocolEndpoints receiver)
       && Map.notMember (fxClientOld fx) (linearBindings (protocolResources sender))
       && Map.notMember (fxServerOld fx) (linearBindings (protocolResources receiver))
       && Map.lookup payloadOccurrence (communicationRestrictedOwners progressed) ==
            Just (fxServerProcess fx, fxPayloadReceiver fx)
       && Map.lookup spectatorOccurrence (communicationRestrictedOwners progressed) ==
            Map.lookup spectatorOccurrence (communicationRestrictedOwners (fxBefore fx)))
    "typed successor head, exact nominal protocol identity, payload or frame drifted"

typedHeadRejectedSource :: Fixture -> Text -> Either String ()
typedHeadRejectedSource fx rejected = do
  (_, badSender, _) <- parseParts rejected
  case typedHeadFrom fx badSender (fxReceiver fx)
      (fxBefore fx) doneOutcome doneOutcome of
    Left (RestrictedTerminalHeadSourceError
      (RestrictedSourceSendError
        (GrammarV1ComponentSendCloseCloseMismatch _ _))) -> Right ()
    other -> Left ("minimally malformed source acquired typed head: " <> show other)

typedHeadWrongOutcome :: Fixture -> Either String ()
typedHeadWrongOutcome fx =
  let wrong = Outcome "NotDone" in
  case typedHeadFrom fx (fxSender fx) (fxReceiver fx)
      (fxBefore fx) doneOutcome wrong of
    Left (RestrictedTerminalHeadOutcomeMismatch process name expected observed) ->
      assert (process == fxServerProcess fx && name == fxServerOld fx
           && expected == doneOutcome && observed == wrong)
        "terminal mismatch did not retain exact peer, predecessor and outcomes"
    other -> Left ("wrong external terminal outcome admitted: " <> show other)

typedHeadWrongSessionHead :: Fixture -> Either String ()
typedHeadWrongSessionHead fx = do
  sender <- requireProtocol (fxClientProcess fx) (fxBefore fx)
  let old = fxClientOld fx
      wrong = ProtocolEndpointBinding old
        (binaryProtocolInstanceRevision (fxInstance fx)) clientRole
        (End doneOutcome)
      changed = sender { protocolEndpoints =
        Map.insert old wrong (protocolEndpoints sender) }
      before = (fxBefore fx) { communicationProtocolContexts =
        Map.insert (fxClientProcess fx) changed
          (communicationProtocolContexts (fxBefore fx)) }
  case typedHeadFrom fx (fxSender fx) (fxReceiver fx)
      before doneOutcome doneOutcome of
    Left (RestrictedTerminalHeadSourceError
      (RestrictedSourceCoreError (RendezvousProtocolError process _))) ->
      assert (process == fxClientProcess fx)
        "wrong-head rejection lost the exact source sender process"
    other -> Left ("wrong original session head acquired typed successor: " <> show other)

typedHeadStaleOriginal :: Fixture -> Either String ()
typedHeadStaleOriginal fx = do
  first <- mapLeft show $ checked fx (fxSender fx) (fxReceiver fx) (fxBefore fx)
  case typedHeadFrom fx (fxSender fx) (fxReceiver fx)
      (restrictedSourceNext first) doneOutcome doneOutcome of
    Left (RestrictedTerminalHeadSourceError
      (RestrictedSourceCoreError
        (RestrictedMessageOwnerMismatch occurrence _ _ process name))) ->
      assert (occurrence == payloadOccurrence
           && process == fxServerProcess fx && name == fxPayloadReceiver fx)
        "stale replay lost exact previously transferred payload identity"
    other -> Left ("consumed predecessor acquired second typed transition: " <> show other)
