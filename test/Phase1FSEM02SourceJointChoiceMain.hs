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
