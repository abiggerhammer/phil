{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: two *independently parsed* component sources, one checked Core
-- joint select/offer transition; this does not certify source architecture binds.
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Process
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax (Branch (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentChoiceRendezvous
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
  clientContext <- mapLeft show $
    insertProtocolEndpoint oldClient revision clientRole
      (protocolProjectionSession clientProjection) emptyProtocolContext
  serverContext <- mapLeft show $
    insertProtocolEndpoint oldServer revision serverRole
      (protocolProjectionSession serverProjection) emptyProtocolContext
  graph <- mapLeft show (instantiateArchitecture rootKey rootSpec)
  staged <- mapLeft show (elaborateProcessNetwork graph [clientSite, serverSite])
  active <- mapLeft show (activateRootProcesses staged)
  let revisionRoot = identityInstanceRevision (processNetworkRoot active)
      clientProcess = deriveProcessKey revisionRoot (processSiteKey clientSite)
      serverProcess = deriveProcessKey revisionRoot (processSiteKey serverSite)
  Right Fixture
    { fxClient = client, fxServer = server, fxInstance = instanceValue
    , fxClientProcess = clientProcess, fxServerProcess = serverProcess
    , fxClientOld = oldClient, fxClientNext = nextClient, fxServerOld = oldServer
    , fxNetwork = active
    , fxContexts = Map.fromList
        [(clientProcess, clientContext), (serverProcess, serverContext)]
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
