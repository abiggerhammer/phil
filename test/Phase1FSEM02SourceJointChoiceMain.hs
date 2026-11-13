{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: two *independently parsed* component sources, one checked Core
-- joint select/offer transition; this does not certify source architecture binds.
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessEndpointClosure
import Phil.Core.Session (SessionError (..))
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax (Branch (..), Mode (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentChoiceRendezvous
import Phil.Surface.GrammarV1.ComponentChoiceStatefulRendezvous
import Phil.Surface.GrammarV1.ComponentOfferCoverage
import Phil.Surface.GrammarV1.ComponentOfferReplay
import Phil.Surface.GrammarV1.ComponentSelectClose
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  go <- TextIO.readFile "test/fixtures/fsem02-source-choice-v1/accepted.phil"
  cancel <- TextIO.readFile "test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil"
  offer <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/accepted.phil"
  wrongBody <- TextIO.readFile "test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil"
  unknown <- TextIO.readFile "test/fixtures/fsem02-source-choice-v1/unknown-label.phil"
  outcomes <- sequence
    [ test "two source Go arms rendezvous, consuming two exact predecessors" (accepted go offer "Go" (Outcome "Done"))
    , test "two source Cancel arms rendezvous, preserving terminal outcomes" (accepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "external peer mismatch rejects before any local step" (peerMismatch go offer)
    , test "bad source offer body rejects exact class, not opaque admission" (wrongBodyRejected go offer wrongBody)
    , test "source unlisted select label rejected by production offer projection" (unlistedSourceLabelRejected unknown offer)
    , test "both predecessor names stale after successful joint step" (staleAfterSuccess go offer)
    , test "client wrong session head rejects joint step" (wrongClientHeadRejected go offer)
    , test "client wrong role cannot reuse valid offer authority" (wrongClientRoleRejected go offer)
    , test "Go source stateful choice moves both endpoint occurrence names" (statefulAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel source stateful choice preserves terminal outcomes" (statefulAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "missing endpoint owner rejects exact occurrence class" (missingEndpointOwnerRejected go offer)
    , test "stolen endpoint owner cannot confer authority" (stolenEndpointOwnerRejected go offer)
    , test "duplicate owner alias is ambiguous, not silently chosen" (ambiguousEndpointOwnerRejected go offer)
    , test "minimally wrong offer body rejects before owner transition" (statefulWrongBodyRejected go offer wrongBody)
    , test "stateful consumed predecessor cannot replay" (statefulStaleRejected go offer)
    , test "stateful wrong session head rejects" (statefulWrongHeadRejected go offer)
    , test "Go source close retires only the chosen client endpoint" (choiceClientCloseAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel source close preserves distinct terminal outcome" (choiceClientCloseAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "wrong selected-client close outcome rejects exact Core class" (choiceClientCloseWrongOutcome go offer)
    , test "source offer wrong body rejects before client close" (choiceClientCloseWrongBody go offer wrongBody)
    , test "stale select/offer predecessor cannot authorize another close" (choiceClientCloseStale go offer)
    , test "missing activation client owner blocks source close" (choiceClientCloseMissingOwner go offer)
    , test "client endpoint cannot be closed twice" (choiceClientCloseTwice go offer)
    , test "Go explicit peer End closure retires both terminal owners" (choiceExplicitPeerAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel explicit peer End closure preserves separate outcome" (choiceExplicitPeerAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "external server wrong End outcome rejects exact Core class" (choiceExplicitPeerWrongOutcome go offer)
    , test "unsupported source offer body rejects before any terminal pair" (choiceExplicitPeerWrongBody go offer wrongBody)
    , test "externally closed server endpoint cannot close twice" (choiceExplicitPeerTwice go offer)
    , test "Go source choice terminal End closes commute under two external outcomes" (choiceCloseDiamondAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel source choice terminal closes commute and preserve spectators" (choiceCloseDiamondAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go choice committed Client/peer half-Close rejects bad peer and retries without rollback"
        (do choiceHalfClosePeerRefusalRetry go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel choice committed Client/peer half-Close preserves Cancel and retries"
        (choiceHalfClosePeerRefusalRetry cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go choice committed half-Close refuses foreign instance and role before retry"
        (do choiceHalfCloseNominalPeerRetry go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel choice committed half-Close refuses nominal peer with exact precedence"
        (choiceHalfCloseNominalPeerRetry cancel offer "Cancel" (Outcome "Cancel"))

    , test "Go source-choice rejected old Select/Offer replay cannot undo either terminal half-Close"
        (do choiceHalfClosePredecessorReplay go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice stale predecessor replay cannot undo committed End"
        (choiceHalfClosePredecessorReplay cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source-choice after both End closes refuses original predecessor and both stale ends"
        (do choiceFullyClosedNoResurrection go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice after either fully closed End order cannot resurrect owners"
        (choiceFullyClosedNoResurrection cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source-choice live End cannot be closed under the opposite process key"
        (do choiceCrossProcessCloseRefusal go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice cross-process refusal preserves both Close orders"
        (choiceCrossProcessCloseRefusal cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source-choice exact process but wrong live terminal End name refuses without consumption"
        (do choiceWrongLocalEndNameRefusal go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice wrong terminal End names preserve both authorized Close orders"
        (choiceWrongLocalEndNameRefusal cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source-choice duplicate live End occurrence refuses ambiguous owner before nominal checks"
        (do choiceTerminalAmbiguousOwnerRefusal go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice ambiguous live End occurrence preserves valid close diamond"
        (choiceTerminalAmbiguousOwnerRefusal cancel offer "Cancel" (Outcome "Cancel")
        )
    , test "Go source-choice near-miss End owners never create false ambiguity"
        (do choiceTerminalNearMissOwnerFilter go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice near-miss owners preserve terminal Close diamond"
        (choiceTerminalNearMissOwnerFilter cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source-choice mixed owner cardinality and exact duplicate ahead of nominal checks"
        (do choiceTerminalMultiAliasCardinality go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source-choice mixed End aliases preserve both valid Close orders"
        (choiceTerminalMultiAliasCardinality cancel offer "Cancel" (Outcome "Cancel"))
    , test "Go source choice unknown/inactive End process gates precede endpoint and nominal checks"
        (do choiceTerminalActivationGate go offer "Go" (Outcome "Done")
            choiceTypedPrefixWrongBody go offer wrongBody)
    , test "Cancel source choice unknown/inactive terminal End exact errors"
        (choiceTerminalActivationGate cancel offer "Cancel" (Outcome "Cancel"))
    , test "diamond rejects wrong externally authorized peer outcome precisely" (choiceCloseDiamondBadPeer go offer)
    , test "diamond rejects wrong source Client close outcome precisely" (choiceCloseDiamondBadClient go offer)
    , test "diamond rejects minimally malformed source offer before both orders" (choiceCloseDiamondWrongBody go offer wrongBody)
    , test "diamond rejects already consumed predecessor without fallback" (choiceCloseDiamondStale go offer)
    , test "peer-first terminal close cannot reuse retired server endpoint" (choiceCloseDiamondPeerDoubleClose go offer)
    , test "Go source-choice predecessor to successor to both terminal orders" (choiceSourceTraceAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel source-choice predecessor trace preserves external branch outcome" (choiceSourceTraceAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "source-choice trace refuses fabricated original occurrence" (choiceSourceTraceMissingOccurrence go offer)
    , test "source-choice trace refuses aliased endpoint occurrence keys" (choiceSourceTraceAliasedOccurrence go offer)
    , test "source-choice trace rejects minimally wrong offer source precisely" (choiceSourceTraceWrongBody go offer wrongBody)
    , test "source-choice trace rejects stale source endpoint rather than replaying" (choiceSourceTraceStale go offer)
    , test "source-choice trace preserves exact wrong terminal outcome class" (choiceSourceTraceWrongPeerOutcome go offer)
    , test "one-sided Client-first and peer-first Go End prefixes are exact" (choiceSourceTraceAccepted go offer "Go" (Outcome "Done"))
    , test "one-sided Client-first and peer-first Cancel End prefixes are exact" (choiceSourceTraceAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "both one-sided End prefixes refuse repeated stale closes" (choiceSourceTracePrefixStale go offer)
    , test "wrong Client End outcome rejects before a successful prefix" (choiceSourceTraceWrongClientOutcome go offer)
    , test "Go choice local Select/Offer and both End prefixes match independent Core steps" (choiceTypedPrefixAccepted go offer "Go" (Outcome "Done"))
    , test "Cancel choice local Select/Offer and both End prefixes match independent Core steps" (choiceTypedPrefixAccepted cancel offer "Cancel" (Outcome "Cancel"))
    , test "typed choice replay rejects minimally wrong offer source exactly" (choiceTypedPrefixWrongBody go offer wrongBody)
    , test "typed choice replay refuses consumed source predecessor exactly" (choiceTypedPrefixStale go offer)
    , test "typed choice replay rejects independently wrong peer End exactly" (choiceTypedPrefixWrongPeerEnd go offer)
    , test "typed choice replay rejects wrong original Select head exactly" (choiceTypedPrefixWrongHead go offer)
    ]
  if and outcomes then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

data Fixture = Fixture
  { fxClient :: GrammarV1ComponentDecl
  , fxServer :: GrammarV1ComponentDecl
  , fxInstance :: BinaryProtocolInstance
  , fxClientProcess :: ProcessKey
  , fxServerProcess :: ProcessKey
  , fxClientOld :: Name
  , fxClientNext :: Name
  , fxServerOld :: Name
  , fxNetwork :: ProcessNetwork
  , fxContexts :: Map.Map ProcessKey ProtocolContext
  , fxState :: ProcessCommunicationState
  }

clientRoot, serverRoot, protocolRoot :: DeclarationKey
clientRoot = DeclarationKey "component.ClientWorker"
serverRoot = DeclarationKey "component.ServerWorker"
protocolRoot = DeclarationKey "protocol.Choice"

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

serverNext :: Name
serverNext = Name "fsem02.server.after"

clientOccurrence, serverOccurrence, spectatorOccurrence, duplicateOccurrence :: ActivationOccurrenceKey
clientOccurrence = ActivationOccurrenceKey "fsem02.client.endpoint"
serverOccurrence = ActivationOccurrenceKey "fsem02.server.endpoint"
spectatorOccurrence = ActivationOccurrenceKey "fsem02.client.spectator"
duplicateOccurrence = ActivationOccurrenceKey "fsem02.client.duplicate"

spectatorName :: Name
spectatorName = Name "fsem02.client.spectator"

parsePair :: Text -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl)
parsePair input = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-source-joint-choice" input)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  case (protocols, components, programs) of
    ([p], [c], [_]) -> Right (p,c)
    _ -> Left "expected complete protocol, component, and root program witness"

fixture :: Text -> Text -> Either String Fixture
fixture clientInput serverInput = do
  (clientProtocol, client) <- parsePair clientInput
  (serverProtocol, server) <- parsePair serverInput
  familyClient <- sourceFamily clientProtocol
  familyServer <- sourceFamily serverProtocol
  assert (familyClient == familyServer)
    "two independently parsed protocol declarations had unequal checked identity"
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy familyClient [] []
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  selected <- case grammarV1CheckedComponentSelectClose clientRoot client of
    Just (Right result) -> Right result
    other -> Left ("not a checked select/close source shape: " <> show other)
  covered <- case grammarV1CheckedComponentOfferCoverage
      serverRoot server (protocolProjectionSession serverProjection) of
    Just (Right result) -> Right result
    other -> Left ("not exact checked source offer coverage: " <> show other)
  assert (protocolProjectionSession clientProjection == Select branches
       && protocolProjectionSession serverProjection == Offer branches)
    "independent source projection was not the exact binary dual"
  let oldClient = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectEndpoint selected)
      nextClient = grammarV1ResolvedBinderCoreName
        (checkedComponentSelectSuccessor selected)
      oldServer = grammarV1ResolvedBinderCoreName
        (checkedComponentOfferEndpoint covered)
      revision = binaryProtocolInstanceRevision instanceValue
  clientBase <- mapLeft show $
    insertProtocolEndpoint oldClient revision clientRole
      (protocolProjectionSession clientProjection) emptyProtocolContext
  clientResources <- mapLeft show $
    insertBinding Affine spectatorName (TyOpaque "Spectator")
      (protocolResources clientBase)
  let clientContext = clientBase { protocolResources = clientResources }
  serverContext <- mapLeft show $
    insertProtocolEndpoint oldServer revision serverRole
      (protocolProjectionSession serverProjection) emptyProtocolContext
  graph <- mapLeft show (instantiateArchitecture rootKey rootSpec)
  staged <- mapLeft show (elaborateProcessNetwork graph [clientSite, serverSite])
  let revisionRoot = identityInstanceRevision (processNetworkRoot staged)
      clientProcess = deriveProcessKey revisionRoot (processSiteKey clientSite)
      serverProcess = deriveProcessKey revisionRoot (processSiteKey serverSite)
      contexts = Map.fromList
        [(clientProcess, clientContext), (serverProcess, serverContext)]
      clientContract = ProcessActivationContract clientProcess
        [ endpointActivation clientOccurrence oldClient
            (protocolProjectionSession clientProjection)
        , ActivationBinding
            { activationOccurrenceKey = spectatorOccurrence
            , activationLocalName = spectatorName
            , activationCheckedTypeMode = CheckedTypeMode (TyOpaque "Spectator") Affine
            , activationBindingOrigin = ExplicitAuthorityOrigin "client.spectator"
            , activationReachability = DirectStatefulReachability spectatorOccurrence
            , activationStartsSharedLoan = False
            }
        ]
      serverContract = ProcessActivationContract serverProcess
        [endpointActivation serverOccurrence oldServer
           (protocolProjectionSession serverProjection)]
  (active, activationState) <- mapLeft show $
    activateProcessState staged [clientContract, serverContract]
  state <- mapLeft show $ communicationStateFromActivation activationState contexts
  Right Fixture
    { fxClient = client, fxServer = server, fxInstance = instanceValue
    , fxClientProcess = clientProcess, fxServerProcess = serverProcess
    , fxClientOld = oldClient, fxClientNext = nextClient, fxServerOld = oldServer
    , fxNetwork = active
    , fxContexts = contexts, fxState = state
    }

endpointActivation :: ActivationOccurrenceKey -> Name -> Session -> ActivationBinding
endpointActivation occurrence endpoint session = ActivationBinding
  { activationOccurrenceKey = occurrence
  , activationLocalName = endpoint
  , activationCheckedTypeMode = CheckedTypeMode (TyEndpoint session) Linear
  , activationBindingOrigin = ProtocolEndpointOrigin "checked source projection"
  , activationReachability = ProtocolMediatedReachability occurrence
  , activationStartsSharedLoan = False
  }

sourceFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
sourceFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily
      protocolRoot (InterfaceRevision "protocol.Choice.v1") protocol of
    Just (Right family) -> Right family
    other -> Left ("production source protocol family did not check: " <> show other)

joint :: Fixture -> Text -> Map.Map ProcessKey ProtocolContext
      -> Either GrammarV1ChoiceRendezvousError GrammarV1ChoiceRendezvous
joint fx peerLabel contexts =
  grammarV1CheckJointSourceChoice
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    serverNext peerLabel (fxNetwork fx) contexts

accepted :: Text -> Text -> Text -> Outcome -> Either String ()
accepted client server label outcome = do
  fx <- fixture client server
  result <- mapLeft show (joint fx label (fxContexts fx))
  assert (checkedComponentSelectLabel (jointChoiceSelectedSource result) == label
       && replayedComponentOfferLabel (jointChoiceCheckedOffer result) == label)
    "joint step label was not checked from each actual source"
  let next = jointChoiceContexts result
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      expected = TyEndpoint (End outcome)
  assert (Map.keysSet next == Map.keysSet (fxContexts fx))
    "joint step added or lost a process context"
  checkSide next (fxClientProcess fx) (fxClientOld fx) (fxClientNext fx)
    expected revision clientRole
  checkSide next (fxServerProcess fx) (fxServerOld fx) serverNext
    expected revision serverRole

checkSide :: Map.Map ProcessKey ProtocolContext -> ProcessKey -> Name -> Name
          -> Ty -> ProtocolInstanceRevision -> ProtocolRoleKey -> Either String ()
checkSide next process old new expected revision role = do
  ctx <- maybe (Left "missing progressed process") Right (Map.lookup process next)
  assert (Map.notMember old (protocolEndpoints ctx)
       && Map.notMember old (linearBindings (protocolResources ctx))
       && Map.lookup new (linearBindings (protocolResources ctx)) == Just expected)
    "one endpoint was reused or its exact successor type lost"
  successor <- maybe (Left "successor metadata missing") Right (lookupProtocolEndpoint new ctx)
  assert (protocolEndpointInstance successor == revision
       && protocolEndpointRole successor == role
       && TyEndpoint (protocolEndpointSession successor) == expected)
    "typed successor lost exact role/instance/terminal obligation"

peerMismatch :: Text -> Text -> Either String ()
peerMismatch client server = do
  fx <- fixture client server
  case joint fx "Cancel" (fxContexts fx) of
    Left (GrammarV1JointChoicePeerLabelMismatch "Go" "Cancel") -> Right ()
    other -> Left ("mismatched peer choice not rejected: " <> show other)

wrongBodyRejected :: Text -> Text -> Text -> Either String ()
wrongBodyRejected client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  let changed = fx {fxServer = badServer}
  case joint changed "Go" (fxContexts fx) of
    Left (GrammarV1JointChoiceOfferSourceError
      (GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported)) -> Right ()
    other -> Left ("minimally bad source arm was not rejected exactly: " <> show other)

unlistedSourceLabelRejected :: Text -> Text -> Either String ()
unlistedSourceLabelRejected client server = do
  fx <- fixture client server
  case joint fx "Absent" (fxContexts fx) of
    Left (GrammarV1JointChoiceOfferSourceError
      (GrammarV1OfferReplayUnlistedLabel "Absent")) -> Right ()
    other -> Left ("unlisted source label admitted: " <> show other)

staleAfterSuccess :: Text -> Text -> Either String ()
staleAfterSuccess client server = do
  fx <- fixture client server
  first <- mapLeft show (joint fx "Go" (fxContexts fx))
  let progressed = jointChoiceContexts first
  checkSide progressed (fxClientProcess fx) (fxClientOld fx) (fxClientNext fx)
    (TyEndpoint (End (Outcome "Done")))
    (binaryProtocolInstanceRevision (fxInstance fx)) clientRole
  case joint fx "Go" progressed of
    Left (GrammarV1JointChoiceOfferSourceError
      (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown old))) ->
        assert (old == fxServerOld fx) "stale rejection lost original offer name"
    other -> Left ("second use of stale predecessor admitted: " <> show other)

wrongClientHeadRejected :: Text -> Text -> Either String ()
wrongClientHeadRejected client server = do
  fx <- fixture client server
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  wrong <- mapLeft show $ insertProtocolEndpoint
    (fxClientOld fx) revision clientRole (End (Outcome "Done")) emptyProtocolContext
  let contexts = Map.insert (fxClientProcess fx) wrong (fxContexts fx)
  case joint fx "Go" contexts of
    Left (GrammarV1JointChoiceCoreError
      (RendezvousProjectionSessionMismatch actual expected observed)) ->
        assert (actual == fxClientProcess fx
             && expected == Select branches && observed == End (Outcome "Done"))
          "wrong head error lost exact original/external projection"
    other -> Left ("wrong selector session head admitted: " <> show other)

wrongClientRoleRejected :: Text -> Text -> Either String ()
wrongClientRoleRejected client server = do
  fx <- fixture client server
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  wrong <- mapLeft show $ insertProtocolEndpoint
    (fxClientOld fx) revision serverRole (Select branches) emptyProtocolContext
  let contexts = Map.insert (fxClientProcess fx) wrong (fxContexts fx)
  case joint fx "Go" contexts of
    Left (GrammarV1JointChoiceCoreError
      (RendezvousProtocolRoleMismatch actual expected observed)) ->
        assert (actual == fxClientProcess fx && expected == clientRole
             && observed == serverRole)
          "wrong role error did not preserve peer and request identity"
    other -> Left ("role mismatch admitted via shared session syntax: " <> show other)


-- This second step consumes a genuine activation-created owner index. The
-- endpoint-only source precheck is never itself an authority to move owners.
stateful :: Fixture -> Text -> ProcessCommunicationState
         -> Either GrammarV1StatefulChoiceError GrammarV1StatefulChoice
stateful fx label state =
  grammarV1CheckStatefulSourceChoice
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    serverNext label (fxNetwork fx) state

statefulAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
statefulAccepted client server label outcome = do
  fx <- fixture client server
  result <- mapLeft show (stateful fx label (fxState fx))
  again <- mapLeft show (stateful fx label (fxState fx))
  assert (result == again) "stateful exact-input replay is nondeterministic"
  let after = statefulChoiceSuccessor result
      owners = communicationRestrictedOwners after
      beforeOwners = communicationRestrictedOwners (fxState fx)
      contexts = communicationProtocolContexts after
      revision = binaryProtocolInstanceRevision (fxInstance fx)
  assert (contexts == jointChoiceContexts (statefulChoiceSourceReplay result))
    "stateful and source-checked contexts diverged"
  assert (Map.keysSet owners == Map.keysSet beforeOwners)
    "stateful choice added or removed a restricted occurrence"
  assert (Map.lookup clientOccurrence owners == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence owners == Just (fxServerProcess fx, serverNext))
    "exact endpoint occurrence was not renamed to its checked successor"
  assert (Map.lookup spectatorOccurrence owners == Map.lookup spectatorOccurrence beforeOwners
       && Map.lookup spectatorOccurrence owners == Just (fxClientProcess fx, spectatorName))
    "independent affine spectator was moved or dropped"
  checkSide contexts (fxClientProcess fx) (fxClientOld fx) (fxClientNext fx)
    (TyEndpoint (End outcome)) revision clientRole
  checkSide contexts (fxServerProcess fx) (fxServerOld fx) serverNext
    (TyEndpoint (End outcome)) revision serverRole

missingEndpointOwnerRejected :: Text -> Text -> Either String ()
missingEndpointOwnerRejected client server = do
  fx <- fixture client server
  let bad = (fxState fx)
        { communicationRestrictedOwners =
            Map.delete clientOccurrence (communicationRestrictedOwners (fxState fx)) }
  case stateful fx "Go" bad of
    Left (GrammarV1StatefulChoiceOwnerError
      (RendezvousEndpointOccurrenceUnknown process endpoint)) ->
        assert (process == fxClientProcess fx && endpoint == fxClientOld fx)
          "missing endpoint owner rejection lost process/name"
    other -> Left ("missing occurrence advanced: " <> show other)

stolenEndpointOwnerRejected :: Text -> Text -> Either String ()
stolenEndpointOwnerRejected client server = do
  fx <- fixture client server
  let bad = (fxState fx)
        { communicationRestrictedOwners =
            Map.insert clientOccurrence (fxServerProcess fx, fxClientOld fx)
              (communicationRestrictedOwners (fxState fx)) }
  case stateful fx "Go" bad of
    Left (GrammarV1StatefulChoiceOwnerError
      (RendezvousEndpointOccurrenceUnknown process endpoint)) ->
        assert (process == fxClientProcess fx && endpoint == fxClientOld fx)
          "stolen owner rejection lost exact identity"
    other -> Left ("wrong-process owner advanced: " <> show other)

ambiguousEndpointOwnerRejected :: Text -> Text -> Either String ()
ambiguousEndpointOwnerRejected client server = do
  fx <- fixture client server
  let bad = (fxState fx)
        { communicationRestrictedOwners =
            Map.insert duplicateOccurrence (fxClientProcess fx, fxClientOld fx)
              (communicationRestrictedOwners (fxState fx)) }
  case stateful fx "Go" bad of
    Left (GrammarV1StatefulChoiceOwnerError
      (RendezvousEndpointOccurrenceAmbiguous process endpoint occurrences)) ->
        assert (process == fxClientProcess fx && endpoint == fxClientOld fx
             && length occurrences == 2
             && clientOccurrence `elem` occurrences
             && duplicateOccurrence `elem` occurrences)
          "ambiguous endpoint diagnostic lost the two exact occurrences"
    other -> Left ("duplicate alias silently chosen: " <> show other)

statefulWrongBodyRejected :: Text -> Text -> Text -> Either String ()
statefulWrongBodyRejected client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  let changed = fx {fxServer = badServer}
  case stateful changed "Go" (fxState fx) of
    Left (GrammarV1StatefulChoiceSourceError
      (GrammarV1JointChoiceOfferSourceError
        (GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported))) ->
          Right ()
    other -> Left ("stateful wrong source body failed exact rejection: " <> show other)

statefulStaleRejected :: Text -> Text -> Either String ()
statefulStaleRejected client server = do
  fx <- fixture client server
  first <- mapLeft show (stateful fx "Go" (fxState fx))
  case stateful fx "Go" (statefulChoiceSuccessor first) of
    Left (GrammarV1StatefulChoiceSourceError
      (GrammarV1JointChoiceOfferSourceError
        (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown endpoint)))) ->
          assert (endpoint == fxServerOld fx) "stale rejection named wrong source endpoint"
    other -> Left ("consumed stateful source endpoint was reused: " <> show other)

statefulWrongHeadRejected :: Text -> Text -> Either String ()
statefulWrongHeadRejected client server = do
  fx <- fixture client server
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  wrong <- mapLeft show $ insertProtocolEndpoint
    (fxClientOld fx) revision clientRole (End (Outcome "Done")) emptyProtocolContext
  let bad = (fxState fx)
        { communicationProtocolContexts = Map.insert
            (fxClientProcess fx) wrong (communicationProtocolContexts (fxState fx)) }
  case stateful fx "Go" bad of
    Left (GrammarV1StatefulChoiceSourceError
      (GrammarV1JointChoiceCoreError
        (RendezvousProjectionSessionMismatch process expected actual))) ->
          assert (process == fxClientProcess fx
               && expected == Select branches && actual == End (Outcome "Done"))
            "stateful mismatch lost the exact original head and observed state"
    other -> Left ("stateful wrong head advanced: " <> show other)


-- FSEM-02: source-level 'close chosen' is a real Core terminal endpoint
-- transition, but the source offer arm returns unit: it does NOT close the
-- independent server endpoint or discharge that process/root's obligations.
choiceClientCloseFrom
  :: Fixture -> Text -> Outcome -> ProcessCommunicationState
  -> Either GrammarV1StatefulChoiceClientCloseError
       GrammarV1StatefulChoiceClientClose
choiceClientCloseFrom fx label outcome state =
  grammarV1CloseStatefulSourceChoiceClient
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    serverNext label (fxNetwork fx) state outcome

choiceClientClose
  :: Fixture -> Text -> Outcome
  -> Either GrammarV1StatefulChoiceClientCloseError
       GrammarV1StatefulChoiceClientClose
choiceClientClose fx label outcome =
  choiceClientCloseFrom fx label outcome (fxState fx)

choiceClientCloseAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
choiceClientCloseAccepted client server label outcome = do
  fx <- fixture client server
  checked <- mapLeft show $ choiceClientClose fx label outcome
  again <- mapLeft show $ choiceClientClose fx label outcome
  assert (checked == again) "source select/offer/client-close replay changed with identical inputs"
  let progressed = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay checked)
      final = statefulChoiceClientCloseSuccessor checked
      endpoint = statefulChoiceClientCloseEndpoint checked
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      afterOwners = communicationRestrictedOwners final
      beforeOwners = communicationRestrictedOwners progressed
      afterContexts = communicationProtocolContexts final
  assert (endpoint == fxClientNext fx)
    "the actually closed client endpoint did not come from the checked source binder"
  independent <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) progressed
      (fxClientProcess fx) (fxClientNext fx) revision clientRole outcome
  assert (final == independent)
    "source client-close result diverged from independent native Core close replay"
  assert (Map.lookup clientOccurrence afterOwners == Nothing
       && Map.lookup serverOccurrence afterOwners == Just (fxServerProcess fx, serverNext)
       && Map.lookup spectatorOccurrence afterOwners == Map.lookup spectatorOccurrence beforeOwners
       && Map.keysSet beforeOwners == Map.keysSet (Map.insert clientOccurrence
            (fxClientProcess fx, fxClientNext fx) afterOwners))
    "client-close owner retirement changed the peer or spectator ledger"
  clientContext <- maybe (Left "client context missing after close")
    Right (Map.lookup (fxClientProcess fx) afterContexts)
  assert (Map.notMember (fxClientOld fx) (protocolEndpoints clientContext)
       && Map.notMember endpoint (protocolEndpoints clientContext)
       && Map.notMember endpoint (linearBindings (protocolResources clientContext)))
    "closed client's endpoint still lives in protocol or resource state"
  checkSide afterContexts (fxServerProcess fx) (fxServerOld fx) serverNext
    (TyEndpoint (End outcome)) revision serverRole

choiceClientCloseWrongOutcome :: Text -> Text -> Either String ()
choiceClientCloseWrongOutcome client server = do
  fx <- fixture client server
  case choiceClientClose fx "Go" (Outcome "Cancel") of
    Left (GrammarV1StatefulChoiceClientCloseCoreError
      (EndpointClosureProtocolError process
        (ProtocolSessionError (CloseOutcomeMismatch
          (Outcome "Done") (Outcome "Cancel"))))) ->
      assert (process == fxClientProcess fx) "close error lost original client process"
    other -> Left ("wrong close outcome was not rejected by actual Core: " <> show other)

choiceClientCloseWrongBody :: Text -> Text -> Text -> Either String ()
choiceClientCloseWrongBody client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  case choiceClientClose (fx { fxServer = badServer }) "Go" (Outcome "Done") of
    Left (GrammarV1StatefulChoiceClientCloseSourceError
      (GrammarV1StatefulChoiceSourceError
        (GrammarV1JointChoiceOfferSourceError
          (GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported)))) ->
      Right ()
    other -> Left ("unsupported source arm was silently admitted: " <> show other)

choiceClientCloseStale :: Text -> Text -> Either String ()
choiceClientCloseStale client server = do
  fx <- fixture client server
  first <- mapLeft show $ stateful fx "Go" (fxState fx)
  case choiceClientCloseFrom fx "Go" (Outcome "Done")
      (statefulChoiceSuccessor first) of
    Left (GrammarV1StatefulChoiceClientCloseSourceError
      (GrammarV1StatefulChoiceSourceError
        (GrammarV1JointChoiceOfferSourceError
          (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown endpoint))))) ->
      assert (endpoint == fxServerOld fx) "stale error named another endpoint"
    other -> Left ("stale source endpoint was reaccepted: " <> show other)

choiceClientCloseMissingOwner :: Text -> Text -> Either String ()
choiceClientCloseMissingOwner client server = do
  fx <- fixture client server
  let bad = (fxState fx)
        { communicationRestrictedOwners =
            Map.delete clientOccurrence (communicationRestrictedOwners (fxState fx)) }
  case choiceClientCloseFrom fx "Go" (Outcome "Done") bad of
    Left (GrammarV1StatefulChoiceClientCloseSourceError
      (GrammarV1StatefulChoiceOwnerError
        (RendezvousEndpointOccurrenceUnknown process endpoint))) ->
      assert (process == fxClientProcess fx && endpoint == fxClientOld fx)
        "owner-index rejection lost exact process/endpoint"
    other -> Left ("missing owner accepted before client close: " <> show other)

choiceClientCloseTwice :: Text -> Text -> Either String ()
choiceClientCloseTwice client server = do
  fx <- fixture client server
  first <- mapLeft show $ choiceClientClose fx "Go" (Outcome "Done")
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  case closeProcessEndpointState (fxNetwork fx)
      (statefulChoiceClientCloseSuccessor first)
      (fxClientProcess fx) (fxClientNext fx) revision clientRole
      (Outcome "Done") of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxClientProcess fx && endpoint == fxClientNext fx)
        "duplicate close lost its exact endpoint/process"
    other -> Left ("second close returned a successor: " <> show other)

-- The offer arm returns unit and cannot authorize this action. The second
-- Outcome is an independent, explicit trusted caller input checked by Core.
choiceExplicitPeerFrom
  :: Fixture -> Text -> Outcome -> Outcome -> ProcessCommunicationState
  -> Either GrammarV1StatefulChoiceExplicitPeerCloseError
       GrammarV1StatefulChoiceExplicitPeerClose
choiceExplicitPeerFrom fx label clientOutcome peerOutcome state =
  grammarV1CloseStatefulSourceChoiceExplicitPeer
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    serverNext label (fxNetwork fx) state clientOutcome peerOutcome

choiceExplicitPeer
  :: Fixture -> Text -> Outcome -> Outcome
  -> Either GrammarV1StatefulChoiceExplicitPeerCloseError
       GrammarV1StatefulChoiceExplicitPeerClose
choiceExplicitPeer fx label clientOutcome peerOutcome =
  choiceExplicitPeerFrom fx label clientOutcome peerOutcome (fxState fx)

choiceExplicitPeerAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
choiceExplicitPeerAccepted client server label outcome = do
  fx <- fixture client server
  result <- mapLeft show $ choiceExplicitPeer fx label outcome outcome
  repeatResult <- mapLeft show $ choiceExplicitPeer fx label outcome outcome
  assert (result == repeatResult) "explicit peer terminal replay is nondeterministic"
  let afterClient = statefulChoiceClientCloseSuccessor
        (statefulChoiceExplicitPeerCloseClient result)
      final = statefulChoiceExplicitPeerCloseSuccessor result
      owners = communicationRestrictedOwners final
      beforeOwners = communicationRestrictedOwners (fxState fx)
      contexts = communicationProtocolContexts final
      revision = binaryProtocolInstanceRevision (fxInstance fx)
  independent <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) afterClient
      (fxServerProcess fx) serverNext revision serverRole outcome
  assert (final == independent)
    "explicit peer terminal replay diverged from native Core close"
  assert (Map.lookup clientOccurrence owners == Nothing
       && Map.lookup serverOccurrence owners == Nothing
       && Map.lookup spectatorOccurrence owners ==
            Map.lookup spectatorOccurrence beforeOwners
       && Map.keysSet owners ==
            Map.keysSet (Map.delete clientOccurrence
              (Map.delete serverOccurrence beforeOwners)))
    "terminal pair retired wrong owners or changed unrelated spectator"
  clientContext <- maybe (Left "client context vanished") Right
    (Map.lookup (fxClientProcess fx) contexts)
  serverContext <- maybe (Left "server context vanished") Right
    (Map.lookup (fxServerProcess fx) contexts)
  assert (Map.notMember (fxClientNext fx) (protocolEndpoints clientContext)
       && Map.notMember serverNext (protocolEndpoints serverContext)
       && Map.notMember (fxClientNext fx)
            (linearBindings (protocolResources clientContext))
       && Map.notMember serverNext
            (linearBindings (protocolResources serverContext)))
    "terminal pair retained a closed protocol or linear resource"

choiceExplicitPeerWrongOutcome :: Text -> Text -> Either String ()
choiceExplicitPeerWrongOutcome client server = do
  fx <- fixture client server
  case choiceExplicitPeer fx "Go" (Outcome "Done") (Outcome "Cancel") of
    Left (GrammarV1StatefulChoiceExplicitPeerCloseCoreError
      (EndpointClosureProtocolError process
        (ProtocolSessionError (CloseOutcomeMismatch
          (Outcome "Done") (Outcome "Cancel"))))) ->
      assert (process == fxServerProcess fx)
        "wrong peer End outcome lost the rejecting Server process"
    other -> Left ("wrong peer outcome unexpectedly advanced: " <> show other)

choiceExplicitPeerWrongBody :: Text -> Text -> Text -> Either String ()
choiceExplicitPeerWrongBody client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  case choiceExplicitPeer (fx { fxServer = badServer })
      "Go" (Outcome "Done") (Outcome "Done") of
    Left (GrammarV1StatefulChoiceExplicitPeerClosePriorError
      (GrammarV1StatefulChoiceClientCloseSourceError
        (GrammarV1StatefulChoiceSourceError
          (GrammarV1JointChoiceOfferSourceError
            (GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported))))) ->
      Right ()
    other -> Left ("bad source arm unexpectedly authorized terminal pair: " <> show other)

choiceExplicitPeerTwice :: Text -> Text -> Either String ()
choiceExplicitPeerTwice client server = do
  fx <- fixture client server
  result <- mapLeft show $
    choiceExplicitPeer fx "Go" (Outcome "Done") (Outcome "Done")
  let final = statefulChoiceExplicitPeerCloseSuccessor result
      revision = binaryProtocolInstanceRevision (fxInstance fx)
  case closeProcessEndpointState (fxNetwork fx) final
      (fxServerProcess fx) serverNext revision serverRole (Outcome "Done") of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxServerProcess fx && endpoint == serverNext)
        "stale server close lost precise endpoint/process evidence"
    other -> Left ("duplicate Server End closure advanced: " <> show other)

-- The two orders are *explicit* Core choices. The source contains only
-- Client close; a Server return-unit arm cannot authorize peer disposition.
choiceCloseDiamondFrom
  :: Fixture -> Text -> Outcome -> Outcome -> ProcessCommunicationState
  -> Either GrammarV1ChoiceCloseDiamondError GrammarV1ChoiceCloseDiamond
choiceCloseDiamondFrom fx label clientOutcome peerOutcome initial =
  grammarV1CheckSourceChoiceCloseDiamond
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    serverNext label (fxNetwork fx) initial clientOutcome peerOutcome

choiceCloseDiamond
  :: Fixture -> Text -> Outcome -> Outcome
  -> Either GrammarV1ChoiceCloseDiamondError GrammarV1ChoiceCloseDiamond
choiceCloseDiamond fx label clientOutcome peerOutcome =
  choiceCloseDiamondFrom fx label clientOutcome peerOutcome (fxState fx)

choiceCloseDiamondAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
choiceCloseDiamondAccepted client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  again <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  assert (diamond == again) "terminal diamond changed under identical source and external inputs"
  let forward = choiceCloseDiamondForward diamond
      ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient forward))
      peerFirst = choiceCloseDiamondPeerFirst diamond
      after = choiceCloseDiamondReverse diamond
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      ownersBefore = communicationRestrictedOwners ready
      ownersPeerFirst = communicationRestrictedOwners peerFirst
      ownersAfter = communicationRestrictedOwners after
  independentPeerFirst <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) ready
      (fxServerProcess fx) serverNext revision serverRole outcome
  independentClientSecond <- mapLeft show $
    closeProcessEndpointState (fxNetwork fx) independentPeerFirst
      (fxClientProcess fx) (fxClientNext fx) revision clientRole outcome
  assert (peerFirst == independentPeerFirst
       && after == independentClientSecond
       && after == statefulChoiceExplicitPeerCloseSuccessor forward)
    "actual Core close orders did not form the exact full-state diamond"
  assert (Map.lookup serverOccurrence ownersPeerFirst == Nothing
       && Map.lookup clientOccurrence ownersPeerFirst ==
            Map.lookup clientOccurrence ownersBefore
       && Map.lookup spectatorOccurrence ownersPeerFirst ==
            Map.lookup spectatorOccurrence ownersBefore
       && Map.lookup clientOccurrence ownersAfter == Nothing
       && Map.lookup serverOccurrence ownersAfter == Nothing
       && Map.lookup spectatorOccurrence ownersAfter ==
            Map.lookup spectatorOccurrence ownersBefore
       && Map.keysSet ownersAfter ==
            Map.keysSet (Map.delete clientOccurrence
              (Map.delete serverOccurrence ownersBefore)))
    "terminal diamond consumed wrong occurrence or changed affine spectator"

choiceCloseDiamondBadPeer :: Text -> Text -> Either String ()
choiceCloseDiamondBadPeer client server = do
  fx <- fixture client server
  case choiceCloseDiamond fx "Go" (Outcome "Done") (Outcome "Cancel") of
    Left (GrammarV1ChoiceCloseDiamondForwardError
      (GrammarV1StatefulChoiceExplicitPeerCloseCoreError
        (EndpointClosureProtocolError process
          (ProtocolSessionError (CloseOutcomeMismatch
            (Outcome "Done") (Outcome "Cancel")))))) ->
      assert (process == fxServerProcess fx) "wrong peer outcome named wrong process"
    other -> Left ("wrong peer outcome silently reached diamond: " <> show other)

choiceCloseDiamondBadClient :: Text -> Text -> Either String ()
choiceCloseDiamondBadClient client server = do
  fx <- fixture client server
  case choiceCloseDiamond fx "Go" (Outcome "Cancel") (Outcome "Done") of
    Left (GrammarV1ChoiceCloseDiamondForwardError
      (GrammarV1StatefulChoiceExplicitPeerClosePriorError
        (GrammarV1StatefulChoiceClientCloseCoreError
          (EndpointClosureProtocolError process
            (ProtocolSessionError (CloseOutcomeMismatch
              (Outcome "Done") (Outcome "Cancel"))))))) ->
      assert (process == fxClientProcess fx) "wrong client outcome named wrong process"
    other -> Left ("wrong client outcome silently reached diamond: " <> show other)

choiceCloseDiamondWrongBody :: Text -> Text -> Text -> Either String ()
choiceCloseDiamondWrongBody client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  case choiceCloseDiamond (fx { fxServer = badServer })
       "Go" (Outcome "Done") (Outcome "Done") of
    Left (GrammarV1ChoiceCloseDiamondForwardError
      (GrammarV1StatefulChoiceExplicitPeerClosePriorError
        (GrammarV1StatefulChoiceClientCloseSourceError
          (GrammarV1StatefulChoiceSourceError
            (GrammarV1JointChoiceOfferSourceError
              (GrammarV1OfferReplayCoverageError GrammarV1ComponentOfferArmBodyUnsupported)))))) ->
      Right ()
    other -> Left ("malformed offer body silently reached diamond: " <> show other)

choiceCloseDiamondStale :: Text -> Text -> Either String ()
choiceCloseDiamondStale client server = do
  fx <- fixture client server
  first <- mapLeft show $ stateful fx "Go" (fxState fx)
  case choiceCloseDiamondFrom fx "Go" (Outcome "Done") (Outcome "Done")
      (statefulChoiceSuccessor first) of
    Left (GrammarV1ChoiceCloseDiamondForwardError
      (GrammarV1StatefulChoiceExplicitPeerClosePriorError
        (GrammarV1StatefulChoiceClientCloseSourceError
          (GrammarV1StatefulChoiceSourceError
            (GrammarV1JointChoiceOfferSourceError
              (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown endpoint))))))) ->
      assert (endpoint == fxServerOld fx) "stale predecessor named wrong endpoint"
    other -> Left ("stale predecessor unexpectedly reached diamond: " <> show other)

choiceCloseDiamondPeerDoubleClose :: Text -> Text -> Either String ()
choiceCloseDiamondPeerDoubleClose client server = do
  fx <- fixture client server
  diamond <- mapLeft show $
    choiceCloseDiamond fx "Go" (Outcome "Done") (Outcome "Done")
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  case closeProcessEndpointState (fxNetwork fx)
      (choiceCloseDiamondPeerFirst diamond)
      (fxServerProcess fx) serverNext revision serverRole (Outcome "Done") of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxServerProcess fx && endpoint == serverNext)
        "duplicate peer-first close lost its process/endpoint classification"
    other -> Left ("peer-first endpoint was reused: " <> show other)

-- Independently parsed complete Select/Offer source, real activated Core
-- process state, and explicitly supplied terminal End authorizations. A bad
-- attempt after the opposite half-Close is checked on the *already committed*
-- state; it returns no successor or rollback token. Check both Go/Cancel and
-- both first-closer schedules against the ordinary checked terminal diamond.
choiceHalfClosePeerRefusalRetry :: Text -> Text -> Text -> Outcome -> Either String ()
choiceHalfClosePeerRefusalRetry client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let forward = choiceCloseDiamondForward diamond
      ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient forward))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      wrongOutcome =
        if outcome == Outcome "Done" then Outcome "Cancel" else Outcome "Done"
      closeClient state selectedOutcome =
        closeProcessEndpointState (fxNetwork fx) state
          (fxClientProcess fx) (fxClientNext fx)
          revision clientRole selectedOutcome
      closePeer state selectedOutcome =
        closeProcessEndpointState (fxNetwork fx) state
          (fxServerProcess fx) serverNext
          revision serverRole selectedOutcome
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      rejectOutcome side expectedProcess trial =
        case trial of
          Left (EndpointClosureProtocolError actualProcess
            (ProtocolSessionError (CloseOutcomeMismatch expected actual))) ->
              assert (actualProcess == expectedProcess
                   && expected == outcome && actual == wrongOutcome)
                (side <> " lost precise End outcome or process error")
          other -> Left (side <> " accepted wrong End outcome: " <> show other)
      rejectRetired side expectedProcess expectedEndpoint trial =
        case trial of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == expectedProcess
                 && actualEndpoint == expectedEndpoint)
              (side <> " lost exact stale endpoint occurrence")
          other -> Left (side <> " reused retired endpoint: " <> show other)
  firstClient <- mapLeft show $ closeClient ready outcome
  assert (Map.lookup (fxServerProcess fx) (contexts firstClient)
            == Map.lookup (fxServerProcess fx) (contexts ready)
       && Map.lookup clientOccurrence (owners firstClient) == Nothing
       && Map.lookup serverOccurrence (owners firstClient)
            == Map.lookup serverOccurrence (owners ready)
       && Map.lookup spectatorOccurrence (owners firstClient)
            == Map.lookup spectatorOccurrence (owners ready))
    "Client-first half-Close changed the live peer or borrowed spectator"
  rejectOutcome "Client-first bad Server End" (fxServerProcess fx)
    (closePeer firstClient wrongOutcome)
  rejectRetired "Client-first retired Client" (fxClientProcess fx)
    (fxClientNext fx) (closeClient firstClient outcome)
  afterClientFirst <- mapLeft show $ closePeer firstClient outcome
  firstPeer <- mapLeft show $ closePeer ready outcome
  assert (Map.lookup (fxClientProcess fx) (contexts firstPeer)
            == Map.lookup (fxClientProcess fx) (contexts ready)
       && Map.lookup serverOccurrence (owners firstPeer) == Nothing
       && Map.lookup clientOccurrence (owners firstPeer)
            == Map.lookup clientOccurrence (owners ready)
       && Map.lookup spectatorOccurrence (owners firstPeer)
            == Map.lookup spectatorOccurrence (owners ready))
    "Server-first half-Close changed the live client or borrowed spectator"
  rejectOutcome "Server-first bad Client End" (fxClientProcess fx)
    (closeClient firstPeer wrongOutcome)
  rejectRetired "Server-first retired Server" (fxServerProcess fx)
    serverNext (closePeer firstPeer outcome)
  afterPeerFirst <- mapLeft show $ closeClient firstPeer outcome
  assert (afterClientFirst == afterPeerFirst
       && afterClientFirst == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence (owners afterClientFirst) == Nothing
       && Map.lookup serverOccurrence (owners afterClientFirst) == Nothing
       && Map.lookup spectatorOccurrence (owners afterClientFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "wrong-outcome refusal/retry changed exact two-process final state"

-- FSEM-02: challenge *externally presented* nominal instance and role after
-- one of the source-checked Select/Offer participants has committed End Close.
-- Check both orders and both complete source choices. Rejections return no
-- successor; the state used for the authorized retry is the exact committed
-- state, not a rebuilt/rolled-back one.
choiceHalfCloseNominalPeerRetry :: Text -> Text -> Text -> Outcome -> Either String ()
choiceHalfCloseNominalPeerRetry client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let forward = choiceCloseDiamondForward diamond
      ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient forward))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.foreign.choice.instance"
      foreignRole = ProtocolRoleKey "OtherRole"
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      attempt process endpoint state suppliedRevision suppliedRole =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          suppliedRevision suppliedRole outcome
      clientAttempt = attempt (fxClientProcess fx) (fxClientNext fx)
      peerAttempt = attempt (fxServerProcess fx) serverNext
      nominalCases side process endpoint trial =
        case trial of
          Left (EndpointClosureProtocolError actualProcess
            (ProtocolInstanceMismatch actualEndpoint expected actual)) ->
              assert (actualProcess == process && actualEndpoint == endpoint
                   && expected == foreignRevision && actual == revision)
                (side <> " lost exact instance mismatch or instance-first precedence")
          other -> Left (side <> " did not reject foreign instance: " <> show other)
      wrongRole side process endpoint trial =
        case trial of
          Left (EndpointClosureProtocolError actualProcess
            (ProtocolRoleMismatch actualEndpoint expected actual)) ->
              assert (actualProcess == process && actualEndpoint == endpoint
                   && expected == foreignRole
                   && actual == (if process == fxClientProcess fx then clientRole else serverRole))
                (side <> " lost exact nominal role diagnostic")
          other -> Left (side <> " did not reject foreign role: " <> show other)
      stale side process endpoint trial =
        case trial of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              (side <> " lost retired occurrence precedence")
          other -> Left (side <> " accepted stale endpoint: " <> show other)
      checkNominal side process endpoint committed role attemptClose = do
        nominalCases side process endpoint
          (attemptClose committed foreignRevision role)
        wrongRole side process endpoint
          (attemptClose committed revision foreignRole)
        nominalCases (side <> " both-wrong") process endpoint
          (attemptClose committed foreignRevision foreignRole)
  clientFirst <- mapLeft show $ clientAttempt ready revision clientRole
  assert (Map.lookup clientOccurrence (owners clientFirst) == Nothing
       && Map.lookup serverOccurrence (owners clientFirst)
            == Map.lookup serverOccurrence (owners ready)
       && Map.lookup (fxServerProcess fx) (contexts clientFirst)
            == Map.lookup (fxServerProcess fx) (contexts ready)
       && Map.lookup spectatorOccurrence (owners clientFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "client-first nominal trial changed live peer or borrowed spectator"
  checkNominal "client-first peer" (fxServerProcess fx) serverNext
    clientFirst serverRole peerAttempt
  stale "client-first retired client" (fxClientProcess fx) (fxClientNext fx)
    (clientAttempt clientFirst foreignRevision foreignRole)
  afterClientFirst <- mapLeft show $ peerAttempt clientFirst revision serverRole

  peerFirst <- mapLeft show $ peerAttempt ready revision serverRole
  assert (Map.lookup serverOccurrence (owners peerFirst) == Nothing
       && Map.lookup clientOccurrence (owners peerFirst)
            == Map.lookup clientOccurrence (owners ready)
       && Map.lookup (fxClientProcess fx) (contexts peerFirst)
            == Map.lookup (fxClientProcess fx) (contexts ready)
       && Map.lookup spectatorOccurrence (owners peerFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "peer-first nominal trial changed live client or borrowed spectator"
  checkNominal "peer-first client" (fxClientProcess fx) (fxClientNext fx)
    peerFirst clientRole clientAttempt
  stale "peer-first retired peer" (fxServerProcess fx) serverNext
    (peerAttempt peerFirst foreignRevision foreignRole)
  afterPeerFirst <- mapLeft show $ clientAttempt peerFirst revision clientRole
  assert (afterClientFirst == afterPeerFirst
       && afterClientFirst == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence (owners afterPeerFirst) == Nothing
       && Map.lookup serverOccurrence (owners afterPeerFirst) == Nothing
       && Map.lookup spectatorOccurrence (owners afterPeerFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "nominal refusal/retry did not converge to the exact checked End diamond"


-- A source-derived Select/Offer step has already consumed both original
-- predecessors before either terminal Close. A retry of the same complete
-- source against an already committed *one-sided* state must reject the
-- original peer predecessor, not rewind the committed End or confer a new
-- endpoint. The surviving peer still closes using its separate Core grant.
choiceHalfClosePredecessorReplay
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceHalfClosePredecessorReplay client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      closeClient state =
        closeProcessEndpointState (fxNetwork fx) state
          (fxClientProcess fx) (fxClientNext fx)
          revision clientRole outcome
      closePeer state =
        closeProcessEndpointState (fxNetwork fx) state
          (fxServerProcess fx) serverNext
          revision serverRole outcome
      rejectOld side committed =
        case stateful fx label committed of
          Left (GrammarV1StatefulChoiceSourceError
            (GrammarV1JointChoiceOfferSourceError
              (GrammarV1OfferReplayProtocolError
                (ProtocolEndpointUnknown old)))) ->
                  assert (old == fxServerOld fx)
                    (side <> " did not reject the exact consumed source predecessor")
          other -> Left
            (side <> " replayed a consumed Select/Offer predecessor: " <> show other)
  clientFirst <- mapLeft show $ closeClient ready
  rejectOld "Client-first" clientFirst
  assert (Map.lookup clientOccurrence (owners clientFirst) == Nothing
       && Map.lookup serverOccurrence (owners clientFirst)
            == Map.lookup serverOccurrence (owners ready)
       && Map.lookup (fxServerProcess fx) (contexts clientFirst)
            == Map.lookup (fxServerProcess fx) (contexts ready)
       && Map.lookup spectatorOccurrence (owners clientFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "stale replay after Client End changed peer/owner or borrowed spectator"
  afterClientFirst <- mapLeft show $ closePeer clientFirst

  peerFirst <- mapLeft show $ closePeer ready
  rejectOld "Server-first" peerFirst
  assert (Map.lookup serverOccurrence (owners peerFirst) == Nothing
       && Map.lookup clientOccurrence (owners peerFirst)
            == Map.lookup clientOccurrence (owners ready)
       && Map.lookup (fxClientProcess fx) (contexts peerFirst)
            == Map.lookup (fxClientProcess fx) (contexts ready)
       && Map.lookup spectatorOccurrence (owners peerFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "stale replay after Server End changed client/owner or borrowed spectator"
  afterPeerFirst <- mapLeft show $ closeClient peerFirst
  let contextsFinal = contexts afterPeerFirst
      retiredClient = case Map.lookup (fxClientProcess fx) contextsFinal of
        Just ctx -> Map.notMember (fxClientOld fx) (protocolEndpoints ctx)
        Nothing -> False
      retiredPeer = case Map.lookup (fxServerProcess fx) contextsFinal of
        Just ctx -> Map.notMember (fxServerOld fx) (protocolEndpoints ctx)
        Nothing -> False
  assert (afterClientFirst == afterPeerFirst
       && afterPeerFirst == choiceCloseDiamondReverse diamond
       && retiredClient && retiredPeer
       && Map.lookup clientOccurrence (owners afterPeerFirst) == Nothing
       && Map.lookup serverOccurrence (owners afterPeerFirst) == Nothing
       && Map.lookup spectatorOccurrence (owners afterPeerFirst)
            == Map.lookup spectatorOccurrence (owners ready))
    "rejected source replay changed exact final End diamond or resurrected owners"


-- Cross-process identity is an independent authority gate. Even when
-- each active participant has a valid terminal End, the other participant
-- cannot close its endpoint under a substituted process key. Test the exact
-- native occurrence-first error before either End, after one End in each
-- order, and after both Ends; failed attempts return no successor state.
-- The complete Go/Cancel source pair is independently parsed by fixture.
choiceCrossProcessCloseRefusal
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceCrossProcessCloseRefusal client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.cross-process.foreign"
      foreignRole = ProtocolRoleKey "WrongProcessRole"
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      attempt state process endpoint suppliedRevision suppliedRole =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          suppliedRevision suppliedRole outcome
      rightfulClient state =
        attempt state (fxClientProcess fx) (fxClientNext fx)
          revision clientRole
      rightfulPeer state =
        attempt state (fxServerProcess fx) serverNext
          revision serverRole
      rejectCross side state process endpoint =
        case attempt state process endpoint foreignRevision foreignRole of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              (side <> " did not retain exact process/endpoint refusal precedence")
          other -> Left
            (side <> " let a different process adopt a terminal owner: " <> show other)
      checkCross side state = do
        rejectCross (side <> " Client as peer") state
          (fxServerProcess fx) (fxClientNext fx)
        rejectCross (side <> " peer as Client") state
          (fxClientProcess fx) serverNext
  assert (fxClientProcess fx /= fxServerProcess fx)
    "fixture unexpectedly aliases distinct active process identities"
  checkCross "both live" ready
  assert (Map.lookup clientOccurrence (owners ready)
            == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence (owners ready)
            == Just (fxServerProcess fx, serverNext))
    "cross-process refusal changed initial exact endpoint owners"

  clientFirst <- mapLeft show $ rightfulClient ready
  checkCross "Client committed" clientFirst
  assert (Map.lookup (fxServerProcess fx) (contexts clientFirst)
            == Map.lookup (fxServerProcess fx) (contexts ready))
    "Client-first cross-process refusal disturbed the still-live peer"
  afterForward <- mapLeft show $ rightfulPeer clientFirst
  checkCross "Client then peer committed" afterForward

  peerFirst <- mapLeft show $ rightfulPeer ready
  checkCross "peer committed" peerFirst
  assert (Map.lookup (fxClientProcess fx) (contexts peerFirst)
            == Map.lookup (fxClientProcess fx) (contexts ready))
    "peer-first cross-process refusal disturbed the still-live Client"
  afterReverse <- mapLeft show $ rightfulClient peerFirst
  checkCross "peer then Client committed" afterReverse
  assert (afterForward == afterReverse
       && afterForward == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence (owners afterForward) == Nothing
       && Map.lookup serverOccurrence (owners afterForward) == Nothing
       && Map.lookup spectatorOccurrence (owners afterForward)
            == Map.lookup spectatorOccurrence (owners ready))
    "cross-process refusal changed complete terminal state or borrowed spectator"

-- Endpoint spelling is an independent occurrence gate even when the process
-- key is the real ACTIVE owner. A live participant cannot substitute the other
-- participant's terminal name, a consumed predecessor, or a fabricated local
-- name; wrong nominal values must not mask the occurrence-first refusal.
-- These checked Go/Cancel source runs still require separate End authority.
choiceWrongLocalEndNameRefusal
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceWrongLocalEndNameRefusal client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.local-name.foreign"
      foreignRole = ProtocolRoleKey "WrongTerminalRole"
      fabricated = Name "fsem02.local-name.fabricated.end"
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      invalidPairs =
        [ (fxClientProcess fx, serverNext)
        , (fxClientProcess fx, fxClientOld fx)
        , (fxClientProcess fx, fabricated)
        , (fxServerProcess fx, fxClientNext fx)
        , (fxServerProcess fx, fxServerOld fx)
        , (fxServerProcess fx, fabricated)
        ]
      roleFor process =
        if process == fxClientProcess fx then clientRole else serverRole
      attempt state process endpoint suppliedRevision suppliedRole =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          suppliedRevision suppliedRole outcome
      rightfulClient state =
        attempt state (fxClientProcess fx) (fxClientNext fx)
          revision clientRole
      rightfulPeer state =
        attempt state (fxServerProcess fx) serverNext
          revision serverRole
      rejectName side state process endpoint suppliedRevision suppliedRole =
        case attempt state process endpoint suppliedRevision suppliedRole of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              (side <> " lost exact process/name occurrence-first rejection")
          other -> Left
            (side <> " accepted wrong local terminal endpoint: " <> show other)
      checkWrong side state = do
        mapM_ (\(process, endpoint) ->
          rejectName side state process endpoint revision (roleFor process))
          invalidPairs
        mapM_ (\(process, endpoint) ->
          rejectName side state process endpoint foreignRevision foreignRole)
          invalidPairs
  assert (fxClientNext fx /= serverNext
       && fxClientOld fx /= fxClientNext fx
       && fxServerOld fx /= serverNext
       && fabricated /= fxClientNext fx
       && fabricated /= serverNext)
    "source-derived terminal and wrong local endpoint identities alias"
  checkWrong "both successors live" ready
  assert (Map.lookup clientOccurrence (owners ready)
            == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence (owners ready)
            == Just (fxServerProcess fx, serverNext))
    "wrong-name attempt changed live exact source-choice successor owners"

  clientFirst <- mapLeft show $ rightfulClient ready
  checkWrong "Client first" clientFirst
  assert (Map.lookup (fxServerProcess fx) (contexts clientFirst)
            == Map.lookup (fxServerProcess fx) (contexts ready))
    "wrong-name refusal consumed still-live Server context"
  clientThenPeer <- mapLeft show $ rightfulPeer clientFirst
  checkWrong "Client then peer" clientThenPeer

  peerFirst <- mapLeft show $ rightfulPeer ready
  checkWrong "peer first" peerFirst
  assert (Map.lookup (fxClientProcess fx) (contexts peerFirst)
            == Map.lookup (fxClientProcess fx) (contexts ready))
    "wrong-name refusal consumed still-live Client context"
  peerThenClient <- mapLeft show $ rightfulClient peerFirst
  checkWrong "peer then Client" peerThenClient
  assert (clientThenPeer == peerThenClient
       && clientThenPeer == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence (owners clientThenPeer) == Nothing
       && Map.lookup serverOccurrence (owners clientThenPeer) == Nothing
       && Map.lookup spectatorOccurrence (owners clientThenPeer)
            == Map.lookup spectatorOccurrence (owners ready))
    "wrong-name refusal changed full terminal diamond or borrowed affine frame"

-- This deliberately injects a duplicate exact activation-owner occurrence
-- AFTER checked source progression; it is NOT a source-authorized alias.
-- Native End must refuse ambiguity before checking role/revision/outcome.
-- The other participant may close, and dropping ONLY the injected alias
-- restores the same authorized two-order terminal state and affine frame.
choiceTerminalAmbiguousOwnerRefusal
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceTerminalAmbiguousOwnerRefusal client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      owners = communicationRestrictedOwners ready
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.ambiguous.foreign"
      foreignRole = ProtocolRoleKey "AmbiguousForeignRole"
      badOutcome = Outcome "fsem02.ambiguous.unexpected"
      inject process endpoint state = state
        { communicationRestrictedOwners =
            Map.insert duplicateOccurrence (process, endpoint)
              (communicationRestrictedOwners state) }
      clean state = state
        { communicationRestrictedOwners =
            Map.delete duplicateOccurrence (communicationRestrictedOwners state) }
      clientAlias = inject (fxClientProcess fx) (fxClientNext fx) ready
      peerAlias = inject (fxServerProcess fx) serverNext ready
      probe state process endpoint suppliedRevision suppliedRole suppliedOutcome =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          suppliedRevision suppliedRole suppliedOutcome
      expectAmbiguous description state process endpoint exactOccurrence
          (suppliedRevision, suppliedRole, suppliedOutcome) =
        case probe state process endpoint suppliedRevision suppliedRole
               suppliedOutcome of
          Left (EndpointClosureOccurrenceAmbiguous observedProcess
            observedEndpoint occurrences) ->
              assert (observedProcess == process
                   && observedEndpoint == endpoint
                   && length occurrences == 2
                   && exactOccurrence `elem` occurrences
                   && duplicateOccurrence `elem` occurrences)
                (description <> ": ambiguous End lost exact two occurrence keys")
          other -> Left (description <> ": ambiguous End not refused first: "
                        <> show other)
      clientProbes =
        [ (revision, clientRole, outcome)
        , (foreignRevision, foreignRole, badOutcome)
        ]
      peerProbes =
        [ (revision, serverRole, outcome)
        , (foreignRevision, foreignRole, badOutcome)
        ]
      closeClient state = probe state (fxClientProcess fx) (fxClientNext fx)
        revision clientRole outcome
      closePeer state = probe state (fxServerProcess fx) serverNext
        revision serverRole outcome
  assert (Map.notMember duplicateOccurrence owners
       && Map.lookup clientOccurrence owners
          == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence owners
          == Just (fxServerProcess fx, serverNext)
       && Map.lookup spectatorOccurrence owners
          == Just (fxClientProcess fx, spectatorName))
    "checked source-choice owner population cannot support alias test"
  mapM_ (expectAmbiguous "Client duplicate before End" clientAlias
    (fxClientProcess fx) (fxClientNext fx) clientOccurrence) clientProbes
  mapM_ (expectAmbiguous "Server duplicate before End" peerAlias
    (fxServerProcess fx) serverNext serverOccurrence) peerProbes
  peerWhileClientAmbiguous <- mapLeft show $ closePeer clientAlias
  clientWhilePeerAmbiguous <- mapLeft show $ closeClient peerAlias
  mapM_ (expectAmbiguous "Client duplicate after Server End"
    peerWhileClientAmbiguous (fxClientProcess fx) (fxClientNext fx)
    clientOccurrence) clientProbes
  mapM_ (expectAmbiguous "Server duplicate after Client End"
    clientWhilePeerAmbiguous (fxServerProcess fx) serverNext
    serverOccurrence) peerProbes
  assert (clean clientAlias == ready && clean peerAlias == ready)
    "removing the exact adversarial duplicate changed checked ready state"
  clientFinished <- mapLeft show $ closeClient (clean peerWhileClientAmbiguous)
  peerFinished <- mapLeft show $ closePeer (clean clientWhilePeerAmbiguous)
  assert (clientFinished == peerFinished
       && clientFinished == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence
            (communicationRestrictedOwners clientFinished) == Nothing
       && Map.lookup serverOccurrence
            (communicationRestrictedOwners clientFinished) == Nothing
       && Map.lookup spectatorOccurrence
            (communicationRestrictedOwners clientFinished)
          == Map.lookup spectatorOccurrence owners)
    "ambiguous owner refusal or duplicate cleanup altered authorized End diamond"

-- A near-miss owner entry is not an exact duplicate unless both its
-- process and endpoint name match. This is an adversarial Core observation,
-- not a source-authorized occurrence. Both terminal End orders must succeed
-- while preserving unrelated aliases, the affine spectator and stale errors.
choiceTerminalNearMissOwnerFilter
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceTerminalNearMissOwnerFilter client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      owners = communicationRestrictedOwners
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      fabricated = Name "fsem02.nearmiss.unrelated.terminal"
      baseline = choiceCloseDiamondReverse diamond
      nearMisses =
        [ ("foreign process / Client End",
            (fxServerProcess fx, fxClientNext fx))
        , ("Client process / peer End",
            (fxClientProcess fx, serverNext))
        , ("foreign process / unrelated End",
            (fxServerProcess fx, fabricated))
        ]
      inject pair state = state
        { communicationRestrictedOwners =
            Map.insert duplicateOccurrence pair (owners state) }
      clean state = state
        { communicationRestrictedOwners =
            Map.delete duplicateOccurrence (owners state) }
      probe state process endpoint role =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          revision role outcome
      closeClient state =
        probe state (fxClientProcess fx) (fxClientNext fx) clientRole
      closePeer state =
        probe state (fxServerProcess fx) serverNext serverRole
      stale state process endpoint role =
        case probe state process endpoint role of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              "near-miss owner changed exact stale-predecessor rejection"
          other -> Left ("stale predecessor reappeared under near-miss alias: "
                        <> show other)
      checkNear (description, aliasPair) = do
        let injected = inject aliasPair ready
        assert (Map.lookup duplicateOccurrence (owners injected) == Just aliasPair
             && clean injected == ready)
          (description <> ": injected alias did not frame ready state")
        stale injected (fxClientProcess fx) (fxClientOld fx) clientRole
        stale injected (fxServerProcess fx) (fxServerOld fx) serverRole
        clientFirst <- mapLeft show $ closeClient injected
        peerFirst <- mapLeft show $ closePeer injected
        assert (Map.lookup duplicateOccurrence (owners clientFirst)
                  == Just aliasPair
             && Map.lookup duplicateOccurrence (owners peerFirst)
                  == Just aliasPair)
          (description <> ": first End consumed a nonmatching alias")
        clientThenPeer <- mapLeft show $ closePeer clientFirst
        peerThenClient <- mapLeft show $ closeClient peerFirst
        stale clientThenPeer (fxClientProcess fx) (fxClientOld fx) clientRole
        stale peerThenClient (fxServerProcess fx) (fxServerOld fx) serverRole
        assert (clientThenPeer == peerThenClient
             && clean clientThenPeer == baseline
             && Map.lookup duplicateOccurrence (owners clientThenPeer)
                  == Just aliasPair
             && Map.lookup clientOccurrence (owners clientThenPeer) == Nothing
             && Map.lookup serverOccurrence (owners clientThenPeer) == Nothing
             && Map.lookup spectatorOccurrence (owners clientThenPeer)
                  == Map.lookup spectatorOccurrence (owners ready))
          (description <> ": false ambiguity or End diamond/frame divergence")
  assert (Map.notMember duplicateOccurrence (owners ready)
       && fxClientProcess fx /= fxServerProcess fx
       && fxClientNext fx /= serverNext
       && fabricated /= fxClientNext fx
       && fabricated /= serverNext
       && Map.lookup clientOccurrence (owners ready)
            == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence (owners ready)
            == Just (fxServerProcess fx, serverNext))
    "checked source-choice ready state lacks distinct terminal End owners"
  mapM_ checkNear nearMisses


-- Checked source choice plus multiple simultaneous adversarial Core owner
-- near misses. Neither aliases nor their removal are source authority.
choiceTerminalMultiAliasCardinality
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceTerminalMultiAliasCardinality client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      owners = communicationRestrictedOwners
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      fabricated = Name "fsem02.multi.unrelated.terminal"
      nearAliases =
        [ (ActivationOccurrenceKey "fsem02.multi.foreign-process",
            (fxServerProcess fx, fxClientNext fx))
        , (ActivationOccurrenceKey "fsem02.multi.foreign-end",
            (fxClientProcess fx, serverNext))
        , (ActivationOccurrenceKey "fsem02.multi.unrelated",
            (fxServerProcess fx, fabricated))
        ]
      exactAlias =
        (ActivationOccurrenceKey "fsem02.multi.exact",
          (fxClientProcess fx, fxClientNext fx))
      nearKeys = map fst nearAliases
      inject entries state = state
        { communicationRestrictedOwners =
            foldr (uncurry Map.insert) (owners state) entries }
      remove keys state = state
        { communicationRestrictedOwners =
            foldr Map.delete (owners state) keys }
      clean = remove nearKeys
      baseline = choiceCloseDiamondReverse diamond
      attempt state process endpoint rev role result =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          rev role result
      closeClient state = attempt state (fxClientProcess fx)
        (fxClientNext fx) revision clientRole outcome
      closePeer state = attempt state (fxServerProcess fx)
        serverNext revision serverRole outcome
      stale state process endpoint role =
        case attempt state process endpoint revision role outcome of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              "mixed near-miss changed exact stale-predecessor rejection"
          other -> Left ("mixed near-miss resurrected predecessor: " <> show other)
      aliasesFramed state =
        all (\(key, pair) -> Map.lookup key (owners state) == Just pair)
          nearAliases
      runDiamond description mixed = do
        stale mixed (fxClientProcess fx) (fxClientOld fx) clientRole
        stale mixed (fxServerProcess fx) (fxServerOld fx) serverRole
        clientFirst <- mapLeft show (closeClient mixed)
        peerFirst <- mapLeft show (closePeer mixed)
        assert (aliasesFramed clientFirst && aliasesFramed peerFirst)
          (description <> ": first Close changed nonmatching owner")
        clientThenPeer <- mapLeft show (closePeer clientFirst)
        peerThenClient <- mapLeft show (closeClient peerFirst)
        stale clientThenPeer (fxClientProcess fx) (fxClientOld fx) clientRole
        stale peerThenClient (fxServerProcess fx) (fxServerOld fx) serverRole
        assert (clientThenPeer == peerThenClient
             && clean clientThenPeer == baseline
             && aliasesFramed clientThenPeer
             && Map.lookup clientOccurrence (owners clientThenPeer) == Nothing
             && Map.lookup serverOccurrence (owners clientThenPeer) == Nothing
             && Map.lookup spectatorOccurrence (owners clientThenPeer)
                  == Map.lookup spectatorOccurrence (owners ready))
          (description <> ": exact Close diamond or affine frame diverged")
      foreignRevision = ProtocolInstanceRevision "fsem02.multi.foreign"
      foreignRole = ProtocolRoleKey "MultiForeignRole"
      badOutcome = Outcome "fsem02.multi.invalid"
      ambiguous state =
        case attempt state (fxClientProcess fx) (fxClientNext fx)
          foreignRevision foreignRole badOutcome of
          Left (EndpointClosureOccurrenceAmbiguous p n keys) ->
            assert (p == fxClientProcess fx
                 && n == fxClientNext fx
                 && length keys == 2
                 && elem clientOccurrence keys
                 && elem (fst exactAlias) keys)
              "exact duplicate amid near-misses was not refused first"
          other -> Left ("exact duplicate reached nominal gate: " <> show other)
  assert (fxClientProcess fx /= fxServerProcess fx
       && fxClientNext fx /= serverNext
       && fabricated /= fxClientNext fx
       && fabricated /= serverNext
       && all (\key -> Map.notMember key (owners ready))
            (fst exactAlias : nearKeys)
       && Map.lookup clientOccurrence (owners ready)
            == Just (fxClientProcess fx, fxClientNext fx)
       && Map.lookup serverOccurrence (owners ready)
            == Just (fxServerProcess fx, serverNext))
    "checked choice does not have distinct ready owner population"
  let forward = inject nearAliases ready
      backward = inject (reverse nearAliases) ready
  assert (forward == backward && clean forward == ready)
    "Map insertion order changed supplied near-miss Core state"
  runDiamond "forward near-miss insertion" forward
  runDiamond "reversed near-miss insertion" backward
  let withExactDuplicate = inject (exactAlias : nearAliases) ready
  ambiguous withExactDuplicate
  peerClosed <- mapLeft show (closePeer withExactDuplicate)
  ambiguous peerClosed
  assert (aliasesFramed peerClosed
       && Map.lookup (fst exactAlias) (owners peerClosed)
            == Just (snd exactAlias))
    "independent peer Close modified exact ambiguous owner"
  let restored = remove [fst exactAlias] withExactDuplicate
  assert (restored == forward)
    "removing exactly the duplicate changed unrelated owner aliases"
  runDiamond "exact duplicate removed with all near-misses kept" restored

-- Adversarial population observation: NOT a source-derived deactivation step.
-- Unknown or inactive processes must reject before endpoint/nominal checking,
-- even where a previously checked source-choice End context is still present.
choiceTerminalActivationGate
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceTerminalActivationGate client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.activation.foreign"
      foreignRole = ProtocolRoleKey "ForeignActivationRole"
      unknownProcess = ProcessKey "fsem02.activation.unknown.process"
      fabricatedName = Name "fsem02.activation.unknown.endpoint"
      network = fxNetwork fx
      population = processNetworkPopulation network
      inactiveNetwork process =
        network { processNetworkPopulation = Map.adjust
          (\occ -> occ { processOccurrenceActivation = NotActivated })
          process population }
      attempt net state process endpoint suppliedRevision suppliedRole =
        closeProcessEndpointState net state process endpoint
          suppliedRevision suppliedRole outcome
      probes =
        [ (fxClientNext fx, revision, clientRole)
        , (serverNext, foreignRevision, foreignRole)
        , (fabricatedName, foreignRevision, foreignRole)
        ]
      expectUnknown side state (endpoint, suppliedRevision, suppliedRole) =
        case attempt network state unknownProcess endpoint
            suppliedRevision suppliedRole of
          Left (EndpointClosureUnknownProcess actual) ->
            assert (actual == unknownProcess)
              (side <> ": unknown process diagnostic lost exact key")
          other -> Left (side <> ": unknown process close not refused first: "
                         <> show other)
      expectInactive side state process
          (endpoint, suppliedRevision, suppliedRole) =
        case attempt (inactiveNetwork process) state process endpoint
            suppliedRevision suppliedRole of
          Left (EndpointClosureProcessNotActive actual NotActivated) ->
            assert (actual == process)
              (side <> ": inactive process diagnostic lost exact key")
          other -> Left (side <> ": inactive process close not refused first: "
                         <> show other)
      closeClient state = attempt network state (fxClientProcess fx)
        (fxClientNext fx) revision clientRole
      closePeer state = attempt network state (fxServerProcess fx)
        serverNext revision serverRole
  assert (Map.notMember unknownProcess population
       && Map.member (fxClientProcess fx) population
       && Map.member (fxServerProcess fx) population
       && fxClientProcess fx /= fxServerProcess fx)
    "adversarial process key aliases actual source-derived population"
  clientFirst <- mapLeft show (closeClient ready)
  peerFirst <- mapLeft show (closePeer ready)
  clientThenPeer <- mapLeft show (closePeer clientFirst)
  peerThenClient <- mapLeft show (closeClient peerFirst)
  let states =
        [ ("both successors live", ready)
        , ("Client End retired", clientFirst)
        , ("Server End retired", peerFirst)
        , ("Client/Server fully retired", clientThenPeer)
        , ("Server/Client fully retired", peerThenClient)
        ]
  mapM_ (\(side, state) -> do
    mapM_ (expectUnknown side state) probes
    mapM_ (expectInactive side state (fxClientProcess fx)) probes
    mapM_ (expectInactive side state (fxServerProcess fx)) probes) states
  assert (clientThenPeer == peerThenClient
       && clientThenPeer == choiceCloseDiamondReverse diamond
       && Map.lookup clientOccurrence
            (communicationRestrictedOwners clientThenPeer) == Nothing
       && Map.lookup serverOccurrence
            (communicationRestrictedOwners clientThenPeer) == Nothing
       && Map.lookup spectatorOccurrence
            (communicationRestrictedOwners clientThenPeer)
          == Map.lookup spectatorOccurrence
               (communicationRestrictedOwners ready))
    "process-gate refusal changed valid End diamond or affine spectator"

-- Once BOTH separately authorized End operations have committed, no original
-- parsed source choice and no retired terminal endpoint may be reactivated,
-- regardless of closure order or hostile nominal inputs. This checks actual
-- native two-process Core state, not only the finite Rocq owner ledger.
choiceFullyClosedNoResurrection
  :: Text -> Text -> Text -> Outcome -> Either String ()
choiceFullyClosedNoResurrection client server label outcome = do
  fx <- fixture client server
  diamond <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let ready = statefulChoiceSuccessor
        (statefulChoiceClientCloseSourceReplay
          (statefulChoiceExplicitPeerCloseClient
            (choiceCloseDiamondForward diamond)))
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      foreignRevision = ProtocolInstanceRevision "fsem02.closed.foreign.instance"
      foreignRole = ProtocolRoleKey "OtherRole"
      owners = communicationRestrictedOwners
      contexts = communicationProtocolContexts
      attempt state process endpoint suppliedRevision suppliedRole =
        closeProcessEndpointState (fxNetwork fx) state process endpoint
          suppliedRevision suppliedRole outcome
      closeClient state =
        attempt state (fxClientProcess fx) (fxClientNext fx)
          revision clientRole
      closePeer state =
        attempt state (fxServerProcess fx) serverNext
          revision serverRole
      staleChoice side closed =
        case stateful fx label closed of
          Left (GrammarV1StatefulChoiceSourceError
            (GrammarV1JointChoiceOfferSourceError
              (GrammarV1OfferReplayProtocolError
                (ProtocolEndpointUnknown old)))) ->
                  assert (old == fxServerOld fx)
                    (side <> " lost exact consumed source Server predecessor")
          other -> Left (side <> " resurrected old source choice: " <> show other)
      staleEnd side closed process endpoint suppliedRevision suppliedRole =
        case attempt closed process endpoint suppliedRevision suppliedRole of
          Left (EndpointClosureOccurrenceUnknown actualProcess actualEndpoint) ->
            assert (actualProcess == process && actualEndpoint == endpoint)
              (side <> " lost retired endpoint identity or occurrence-first error")
          other -> Left (side <> " accepted retired terminal End: " <> show other)
      verifyFinal side closed = do
        staleChoice side closed
        staleEnd (side <> " Client") closed
          (fxClientProcess fx) (fxClientNext fx) revision clientRole
        staleEnd (side <> " Server") closed
          (fxServerProcess fx) serverNext revision serverRole
        staleEnd (side <> " Client foreign nominal") closed
          (fxClientProcess fx) (fxClientNext fx) foreignRevision foreignRole
        staleEnd (side <> " Server foreign nominal") closed
          (fxServerProcess fx) serverNext foreignRevision foreignRole
        let clientCtx = Map.lookup (fxClientProcess fx) (contexts closed)
            peerCtx = Map.lookup (fxServerProcess fx) (contexts closed)
            oldClientRetired = case clientCtx of
              Just ctx -> Map.notMember (fxClientOld fx) (protocolEndpoints ctx)
              Nothing -> False
            oldPeerRetired = case peerCtx of
              Just ctx -> Map.notMember (fxServerOld fx) (protocolEndpoints ctx)
              Nothing -> False
        assert (Map.lookup clientOccurrence (owners closed) == Nothing
             && Map.lookup serverOccurrence (owners closed) == Nothing
             && Map.lookup spectatorOccurrence (owners closed)
                  == Map.lookup spectatorOccurrence (owners ready)
             && oldClientRetired && oldPeerRetired)
          (side <> " changed both terminal retirements or borrowed affine frame")
  clientFirst <- mapLeft show $ closeClient ready
  afterForward <- mapLeft show $ closePeer clientFirst
  peerFirst <- mapLeft show $ closePeer ready
  afterReverse <- mapLeft show $ closeClient peerFirst
  assert (afterForward == afterReverse
       && afterReverse == choiceCloseDiamondReverse diamond)
    "actual complete End orders differed before stale replay"
  verifyFinal "Client-then-Server" afterForward
  verifyFinal "Server-then-Client" afterReverse

-- A finite, source-relative choice trace, distinct from restricted
-- Bytes[8] send/receive. The offer's successor and both terminal outcomes
-- remain separate external authority: its return-unit arms do not close End.
choiceSourceTraceFrom
  :: Fixture -> ActivationOccurrenceKey -> ActivationOccurrenceKey
  -> Text -> Outcome -> Outcome -> ProcessCommunicationState
  -> Either GrammarV1ChoiceSourceSuccessorTraceError
       GrammarV1ChoiceSourceSuccessorTrace
choiceSourceTraceFrom fx clientKey offerKey label clientOutcome offerOutcome initial =
  grammarV1CheckChoiceSourceSuccessorTrace
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    clientKey offerKey serverNext label (fxNetwork fx) initial
    clientOutcome offerOutcome

choiceSourceTraceAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
choiceSourceTraceAccepted client server label outcome = do
  fx <- fixture client server
  trace <- mapLeft show $
    choiceSourceTraceFrom fx clientOccurrence serverOccurrence
      label outcome outcome (fxState fx)
  again <- mapLeft show $
    choiceSourceTraceFrom fx clientOccurrence serverOccurrence
      label outcome outcome (fxState fx)
  independent <- mapLeft show $ choiceCloseDiamond fx label outcome outcome
  let before = communicationRestrictedOwners (fxState fx)
      ready = choiceSourceTraceReadyOwners trace
      afterClient = choiceSourceTraceAfterClientOwners trace
      afterPeer = choiceSourceTraceAfterPeerOwners trace
      terminal = choiceSourceTraceTerminalOwners trace
      expectedReady = Map.insert clientOccurrence (fxClientProcess fx, fxClientNext fx)
        (Map.insert serverOccurrence (fxServerProcess fx, serverNext) before)
      expectedAfterClient = Map.delete clientOccurrence expectedReady
      expectedAfterPeer = Map.delete serverOccurrence expectedReady
      expectedTerminal = Map.delete clientOccurrence expectedAfterPeer
  assert (trace == again
       && choiceSourceTraceDiamond trace == independent
       && ready == expectedReady
       && afterClient == expectedAfterClient
       && afterPeer == expectedAfterPeer
       && Map.lookup clientOccurrence afterClient == Nothing
       && Map.lookup serverOccurrence afterClient == Just (fxServerProcess fx, serverNext)
       && Map.lookup serverOccurrence afterPeer == Nothing
       && Map.lookup clientOccurrence afterPeer == Just (fxClientProcess fx, fxClientNext fx)
       && terminal == expectedTerminal
       && Map.lookup spectatorOccurrence afterClient == Map.lookup spectatorOccurrence before
       && Map.lookup spectatorOccurrence afterPeer == Map.lookup spectatorOccurrence before
       && Map.lookup spectatorOccurrence ready ==
            Just (fxClientProcess fx, spectatorName)
       && Map.lookup spectatorOccurrence terminal ==
            Map.lookup spectatorOccurrence before)
    "source-choice trace did not preserve exact original/next/terminal owner identities"

choiceSourceTraceMissingOccurrence :: Text -> Text -> Either String ()
choiceSourceTraceMissingOccurrence client server = do
  fx <- fixture client server
  let invented = ActivationOccurrenceKey "fsem02.choice.fabricated"
  case choiceSourceTraceFrom fx invented serverOccurrence "Go"
      (Outcome "Done") (Outcome "Done") (fxState fx) of
    Left (ChoiceSourceTracePredecessorMismatch key expected Nothing) ->
      assert (key == invented && expected == (fxClientProcess fx, fxClientOld fx))
        "fabricated client occurrence lost exact original source binder"
    other -> Left ("fabricated source-choice occurrence was accepted: " <> show other)

choiceSourceTraceAliasedOccurrence :: Text -> Text -> Either String ()
choiceSourceTraceAliasedOccurrence client server = do
  fx <- fixture client server
  case choiceSourceTraceFrom fx clientOccurrence clientOccurrence "Go"
      (Outcome "Done") (Outcome "Done") (fxState fx) of
    Left ChoiceSourceTraceAliasedOccurrence -> Right ()
    other -> Left ("aliased source-choice occurrences were accepted: " <> show other)

choiceSourceTraceWrongBody :: Text -> Text -> Text -> Either String ()
choiceSourceTraceWrongBody client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  case choiceSourceTraceFrom (fx { fxServer = badServer })
       clientOccurrence serverOccurrence "Go"
       (Outcome "Done") (Outcome "Done") (fxState fx) of
    Left (ChoiceSourceTraceDiamondError
      (GrammarV1ChoiceCloseDiamondForwardError
        (GrammarV1StatefulChoiceExplicitPeerClosePriorError
          (GrammarV1StatefulChoiceClientCloseSourceError
            (GrammarV1StatefulChoiceSourceError
              (GrammarV1JointChoiceOfferSourceError
                (GrammarV1OfferReplayCoverageError
                  GrammarV1ComponentOfferArmBodyUnsupported))))))) -> Right ()
    other -> Left ("minimally malformed source offer reached choice trace: " <> show other)

choiceSourceTraceStale :: Text -> Text -> Either String ()
choiceSourceTraceStale client server = do
  fx <- fixture client server
  first <- mapLeft show $ stateful fx "Go" (fxState fx)
  case choiceSourceTraceFrom fx clientOccurrence serverOccurrence "Go"
      (Outcome "Done") (Outcome "Done") (statefulChoiceSuccessor first) of
    Left (ChoiceSourceTraceDiamondError
      (GrammarV1ChoiceCloseDiamondForwardError
        (GrammarV1StatefulChoiceExplicitPeerClosePriorError
          (GrammarV1StatefulChoiceClientCloseSourceError
            (GrammarV1StatefulChoiceSourceError
              (GrammarV1JointChoiceOfferSourceError
                (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown name)))))))) ->
      assert (name == fxServerOld fx) "stale trace rejection changed source offer endpoint"
    other -> Left ("stale source-choice predecessor advanced: " <> show other)

choiceSourceTraceWrongPeerOutcome :: Text -> Text -> Either String ()
choiceSourceTraceWrongPeerOutcome client server = do
  fx <- fixture client server
  case choiceSourceTraceFrom fx clientOccurrence serverOccurrence "Go"
      (Outcome "Done") (Outcome "Cancel") (fxState fx) of
    Left (ChoiceSourceTraceDiamondError
      (GrammarV1ChoiceCloseDiamondForwardError
        (GrammarV1StatefulChoiceExplicitPeerCloseCoreError
          (EndpointClosureProtocolError process
            (ProtocolSessionError (CloseOutcomeMismatch
              (Outcome "Done") (Outcome "Cancel"))))))) ->
      assert (process == fxServerProcess fx)
        "wrong peer End authority lost exact server process classification"
    other -> Left ("wrong externally supplied peer End outcome was accepted: " <> show other)

-- Invalid Client End authority fails with no successful one-sided trace.
choiceSourceTraceWrongClientOutcome :: Text -> Text -> Either String ()
choiceSourceTraceWrongClientOutcome client server = do
  fx <- fixture client server
  case choiceSourceTraceFrom fx clientOccurrence serverOccurrence "Go"
       (Outcome "Cancel") (Outcome "Done") (fxState fx) of
    Left (ChoiceSourceTraceDiamondError
      (GrammarV1ChoiceCloseDiamondForwardError
        (GrammarV1StatefulChoiceExplicitPeerClosePriorError
          (GrammarV1StatefulChoiceClientCloseCoreError
            (EndpointClosureProtocolError process
              (ProtocolSessionError (CloseOutcomeMismatch
                (Outcome "Done") (Outcome "Cancel")))))))) ->
      assert (process == fxClientProcess fx)
        "wrong Client End outcome named wrong process"
    other -> Left ("wrong Client End outcome fabricated a prefix: " <> show other)

-- Verify both native one-sided states are terminal for their own occurrence,
-- while the other live occurrence is retained for its separately granted End.
choiceSourceTracePrefixStale :: Text -> Text -> Either String ()
choiceSourceTracePrefixStale client server = do
  fx <- fixture client server
  trace <- mapLeft show $ choiceSourceTraceFrom fx clientOccurrence serverOccurrence
    "Go" (Outcome "Done") (Outcome "Done") (fxState fx)
  let diamond = choiceSourceTraceDiamond trace
      clientFirst = statefulChoiceClientCloseSuccessor
        (statefulChoiceExplicitPeerCloseClient (choiceCloseDiamondForward diamond))
      peerFirst = choiceCloseDiamondPeerFirst diamond
      revision = binaryProtocolInstanceRevision (fxInstance fx)
  case closeProcessEndpointState (fxNetwork fx) clientFirst
       (fxClientProcess fx) (fxClientNext fx) revision clientRole (Outcome "Done") of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxClientProcess fx && endpoint == fxClientNext fx)
        "Client-first duplicate close named wrong retired endpoint"
    other -> Left ("Client-first prefix reused stale endpoint: " <> show other)
  case closeProcessEndpointState (fxNetwork fx) peerFirst
       (fxServerProcess fx) serverNext revision serverRole (Outcome "Done") of
    Left (EndpointClosureOccurrenceUnknown process endpoint) ->
      assert (process == fxServerProcess fx && endpoint == serverNext)
        "Peer-first duplicate close named wrong retired endpoint"
    other -> Left ("Peer-first prefix reused stale endpoint: " <> show other)

-- FSEM-02 exact independent local-protocol observer. The single Client
-- source 'close' cannot establish the separately authorized Server End.
choiceTypedPrefixFrom
  :: Fixture -> Text -> Outcome -> Outcome -> ProcessCommunicationState
  -> Either GrammarV1ChoiceTypedPrefixError GrammarV1ChoiceTypedPrefix
choiceTypedPrefixFrom fx label clientOutcome peerOutcome initial =
  grammarV1CheckChoiceTypedPrefix
    clientRoot (fxClient fx) serverRoot (fxServer fx) (fxInstance fx)
    clientRole serverRole (fxClientProcess fx) (fxServerProcess fx)
    clientOccurrence serverOccurrence serverNext label (fxNetwork fx) initial
    clientOutcome peerOutcome

choiceTypedPrefixAccepted :: Text -> Text -> Text -> Outcome -> Either String ()
choiceTypedPrefixAccepted client server label outcome = do
  fx <- fixture client server
  checked <- mapLeft show $
    choiceTypedPrefixFrom fx label outcome outcome (fxState fx)
  repeated <- mapLeft show $
    choiceTypedPrefixFrom fx label outcome outcome (fxState fx)
  let selectStep = choiceTypedPrefixSelect checked
      offerStep = choiceTypedPrefixOffer checked
      clientEnd = choiceTypedPrefixClientEnd checked
      peerEnd = choiceTypedPrefixPeerEnd checked
      revision = binaryProtocolInstanceRevision (fxInstance fx)
      expectedEnd = TyEndpoint (End outcome)
      clientBefore = checkedProtocolPredecessor selectStep
      peerBefore = checkedProtocolPredecessor offerStep
      clientNext = checkedProtocolSuccessor selectStep
      peerNext = checkedProtocolSuccessor offerStep
      clientAfter = checkedProtocolContext selectStep
      peerAfter = checkedProtocolContext offerStep
      diamond = choiceSourceTraceDiamond (choiceTypedPrefixSource checked)
      clientFirst = statefulChoiceClientCloseSuccessor
        (statefulChoiceExplicitPeerCloseClient (choiceCloseDiamondForward diamond))
      peerFirst = choiceCloseDiamondPeerFirst diamond
      contexts state = communicationProtocolContexts state
  assert (checked == repeated
       && protocolEndpointName clientBefore == fxClientOld fx
       && protocolEndpointName peerBefore == fxServerOld fx
       && clientNext == Just (ProtocolEndpointBinding
             (fxClientNext fx) revision clientRole (End outcome))
       && peerNext == Just (ProtocolEndpointBinding
             serverNext revision serverRole (End outcome))
       && Map.lookup (fxClientNext fx)
           (linearBindings (protocolResources clientAfter)) == Just expectedEnd
       && Map.lookup serverNext
           (linearBindings (protocolResources peerAfter)) == Just expectedEnd
       && checkedProtocolSuccessor clientEnd == Nothing
       && checkedProtocolSuccessor peerEnd == Nothing
       && Map.lookup (fxClientProcess fx) (contexts clientFirst)
            == Just (checkedProtocolContext clientEnd)
       && Map.lookup (fxServerProcess fx) (contexts clientFirst)
            == Just peerAfter
       && Map.lookup (fxClientProcess fx) (contexts peerFirst)
            == Just clientAfter
       && Map.lookup (fxServerProcess fx) (contexts peerFirst)
            == Just (checkedProtocolContext peerEnd)
       && Map.lookup spectatorOccurrence
            (communicationRestrictedOwners clientFirst)
            == Map.lookup spectatorOccurrence
                 (communicationRestrictedOwners (fxState fx)))
    "native choice/head or one-sided End prefix diverged from independent local replay"

choiceTypedPrefixWrongBody :: Text -> Text -> Text -> Either String ()
choiceTypedPrefixWrongBody client server bad = do
  fx <- fixture client server
  (_, badServer) <- parsePair bad
  let badFixture = fx {fxServer = badServer}
  case choiceTypedPrefixFrom badFixture "Go" (Outcome "Done")
      (Outcome "Done") (fxState fx) of
    Left (ChoiceTypedPrefixSourceError sourceError) -> case sourceError of
      ChoiceSourceTraceDiamondError
        (GrammarV1ChoiceCloseDiamondForwardError
          (GrammarV1StatefulChoiceExplicitPeerClosePriorError
            (GrammarV1StatefulChoiceClientCloseSourceError
              (GrammarV1StatefulChoiceSourceError
                (GrammarV1JointChoiceOfferSourceError
                  (GrammarV1OfferReplayCoverageError
                    GrammarV1ComponentOfferArmBodyUnsupported)))))) -> Right ()
      other -> Left ("wrong nested minimally rejected source class: " <> show other)
    other -> Left ("minimally rejected offer was accepted as typed choice: " <> show other)

choiceTypedPrefixStale :: Text -> Text -> Either String ()
choiceTypedPrefixStale client server = do
  fx <- fixture client server
  first <- mapLeft show $ stateful fx "Go" (fxState fx)
  case choiceTypedPrefixFrom fx "Go" (Outcome "Done") (Outcome "Done")
      (statefulChoiceSuccessor first) of
    Left (ChoiceTypedPrefixSourceError sourceError) -> case sourceError of
      ChoiceSourceTraceDiamondError
        (GrammarV1ChoiceCloseDiamondForwardError
          (GrammarV1StatefulChoiceExplicitPeerClosePriorError
            (GrammarV1StatefulChoiceClientCloseSourceError
              (GrammarV1StatefulChoiceSourceError
                (GrammarV1JointChoiceOfferSourceError
                  (GrammarV1OfferReplayProtocolError
                    (ProtocolEndpointUnknown old))))))) ->
                      assert (old == fxServerOld fx) "wrong stale peer occurrence"
      other -> Left ("wrong exact stale error: " <> show other)
    other -> Left ("stale original choice predecessor was reused: " <> show other)

choiceTypedPrefixWrongPeerEnd :: Text -> Text -> Either String ()
choiceTypedPrefixWrongPeerEnd client server = do
  fx <- fixture client server
  case choiceTypedPrefixFrom fx "Go" (Outcome "Done") (Outcome "Cancel")
      (fxState fx) of
    Left (ChoiceTypedPrefixSourceError sourceError) -> case sourceError of
      ChoiceSourceTraceDiamondError
        (GrammarV1ChoiceCloseDiamondForwardError
          (GrammarV1StatefulChoiceExplicitPeerCloseCoreError
            (EndpointClosureProtocolError process
              (ProtocolSessionError (CloseOutcomeMismatch
                (Outcome "Done") (Outcome "Cancel")))))) ->
                  assert (process == fxServerProcess fx)
                    "wrong terminal outcome named wrong peer"
      other -> Left ("wrong exact peer End error: " <> show other)
    other -> Left ("wrong peer End authority was silently accepted: " <> show other)

choiceTypedPrefixWrongHead :: Text -> Text -> Either String ()
choiceTypedPrefixWrongHead client server = do
  fx <- fixture client server
  let revision = binaryProtocolInstanceRevision (fxInstance fx)
  wrong <- mapLeft show $ insertProtocolEndpoint
    (fxClientOld fx) revision clientRole (End (Outcome "Done")) emptyProtocolContext
  let bad = (fxState fx)
        { communicationProtocolContexts = Map.insert
            (fxClientProcess fx) wrong (communicationProtocolContexts (fxState fx)) }
  case choiceTypedPrefixFrom fx "Go" (Outcome "Done") (Outcome "Done") bad of
    Left (ChoiceTypedPrefixSourceError sourceError) -> case sourceError of
      ChoiceSourceTraceDiamondError
        (GrammarV1ChoiceCloseDiamondForwardError
          (GrammarV1StatefulChoiceExplicitPeerClosePriorError
            (GrammarV1StatefulChoiceClientCloseSourceError
              (GrammarV1StatefulChoiceSourceError
                (GrammarV1JointChoiceCoreError
                  (RendezvousProjectionSessionMismatch process expected actual)))))) ->
                    assert (process == fxClientProcess fx
                         && expected == Select branches
                         && actual == End (Outcome "Done"))
                      "wrong original Select head lost precise rejection evidence"
      other -> Left ("wrong exact session-head error: " <> show other)
    other -> Left ("wrong original Select session was accepted: " <> show other)

branches :: [Branch]
branches =
  [Branch "Go" Nothing (End (Outcome "Done")),
   Branch "Cancel" Nothing (End (Outcome "Cancel"))]

-- These external process sites are a deliberately explicit, checked Core
-- network. The two complete source witnesses have DIFFERENT architectures;
-- this test does not claim to validate a combined source architecture.
rootSpec :: ArchitectureNodeSpec
rootSpec = ArchitectureNodeSpec
  { architectureNodeDeclaration = declaration "root"
  , architectureNodeStaticBindings = Map.empty
  , architectureNodeRequirements = []
  , architectureNodeChildren =
      [ArchitectureChildSpec clientSlot workerSpec,
       ArchitectureChildSpec serverSlot workerSpec]
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
  { declarationPresentation = DeclarationPresentation label []
  , declarationKey = DeclarationKey ("decl-" <> label)
  , declarationInterfaceSemantics = SemanticAtom "interface"
  , declarationDefinitionSemantics = SemanticAtom "definition"
  }

clientSite, serverSite :: ProcessDeclarationSite
clientSite = ProcessDeclarationSite (ProcessSiteKey "client_run") clientTarget
serverSite = ProcessDeclarationSite (ProcessSiteKey "server_run") serverTarget

rootKey, clientTarget, serverTarget :: InstanceKey
rootKey = InstanceKey "fsem02-joint-root"
clientTarget = scopedInstanceKey rootKey clientSlot
serverTarget = scopedInstanceKey rootKey serverSlot

clientSlot, serverSlot :: OccurrenceSlotKey
clientSlot = OccurrenceSlotKey "client"
serverSlot = OccurrenceSlotKey "server"

assert :: Bool -> String -> Either String ()
assert ok detail = if ok then Right () else Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
