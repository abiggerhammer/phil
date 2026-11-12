{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: source-derived Ping heads + production Core.Protocol progression.
-- This checks finite witnesses, not universal Surface-to-Rocq refinement.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Process
import Phil.Core.ProcessRendezvous
import Phil.Core.Context
  ( CheckError (..), ResourceContext (..), insertBinding, startSharedLoan )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session
  ( SessionAction (..), SessionError (..), SessionStep (..), dualSession )
import Phil.Core.Static
import Phil.Core.Syntax (Branch (..), Mode (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentReceiveClose
import Phil.Surface.GrammarV1.ComponentSendClose
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  accepted <- TextIO.readFile "test/fixtures/fsem02-protocol-progression-v1/accepted.phil"
  stale <- TextIO.readFile "test/fixtures/fsem02-protocol-progression-v1/stale-close.phil"
  results <- sequence
    [ test "FSEM-02 checked whole-source Ping heads progress in exact Core send/receive/close state"
        (checkedSourcePingSteps accepted)
    , test "FSEM-02 source Ping terminal Close requires exact nominal instance/role"
        (sourcePingCloseNominalGates accepted)
    , test "FSEM-02 source Ping successor freshness and borrowed spectator frame"
        (sourcePingSuccessorResourceFreshness accepted)
    , test "FSEM-02 source Ping joint successor freshness and atomic peer refusal"
        (sourcePingJointSuccessorAtomicity accepted)
    , test "FSEM-02 source stale close rejects with exact binder mismatch"
        (sourceStaleCloseRejected stale)
    , test "FSEM-02 mismatched session head rejects with precise action error"
        (wrongSessionHeadRejected accepted)
    , test "source-derived Ping Send/Receive require exact nominal instance and role"
        (nominalSourcePingRejected accepted)
    , test "FSEM-02 Core offer selects exact successor, rejects absent label"
        offerHeadAndMissingLabel
    , test "FSEM-02 Core terminal wrong outcome and same-name successor reject exactly"
        closeAndSelfSuccessorRejected
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " <> label) >> pure True
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data SourcePlans = SourcePlans
  { sourceBinaryInstance :: BinaryProtocolInstance
  , sourceClientPlan :: GrammarV1CheckedComponentSendClose
  , sourceServerPlan :: GrammarV1CheckedComponentReceiveClose
  , sourceProtocolInstance :: ProtocolInstanceRevision
  , sourceClientHead :: Session
  , sourceServerHead :: Session
  }

sourcePlans :: Text.Text -> Either String SourcePlans
sourcePlans source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-protocol-progression-v1" source)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  (protocol, client, server) <-
    case (protocols, components, programs) of
      ([p], [c, s], [_]) -> Right (p, c, s)
      _ -> Left "source fixture must have one protocol, two components, and a selected root"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.Ping")
      (InterfaceRevision "protocol.Ping.v1")
      protocol of
    Just (Right value) -> Right value
    other -> Left ("source protocol did not instantiate a checked binary family: " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  clientProjection <- mapLeft show $
    projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $
    projectProtocolRole instanceValue serverRole
  clientPlan <- case grammarV1CheckedComponentSendClose
      (DeclarationKey "component.ClientWorker") client of
    Just (Right checked) -> Right checked
    other -> Left ("source client send/close body was not checked: " <> show other)
  serverPlan <- case grammarV1CheckedComponentReceiveClose
      (DeclarationKey "component.ServerWorker") server of
    Just (Right checked) -> Right checked
    other -> Left ("source server receive/close body was not checked: " <> show other)
  Right SourcePlans
    { sourceBinaryInstance = instanceValue
    , sourceClientPlan = clientPlan
    , sourceServerPlan = serverPlan
    , sourceProtocolInstance = binaryProtocolInstanceRevision instanceValue
    , sourceClientHead = protocolProjectionSession clientProjection
    , sourceServerHead = protocolProjectionSession serverProjection
    }

checkedSourcePingSteps :: Text.Text -> Either String ()
checkedSourcePingSteps source = do
  plans <- sourcePlans source
  let client = sourceClientPlan plans
      server = sourceServerPlan plans
      instanceRevision = sourceProtocolInstance plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
  assert (clientOld /= clientNext && serverOld /= serverNext)
    "source binders were not distinct semantic endpoint occurrences"
  assert (sourceClientHead plans == Send (Name "x") (TyUInt 8) (End done))
    "source protocol did not project the exact client send state"
  assert (sourceServerHead plans == Receive (Name "x") (TyUInt 8) (End done))
    "source protocol did not project the exact server receive state"
  clientContext <- mapLeft show $
    insertProtocolEndpoint clientOld instanceRevision clientRole
      (sourceClientHead plans) emptyProtocolContext
  serverContext <- mapLeft show $
    insertProtocolEndpoint serverOld instanceRevision serverRole
      (sourceServerHead plans) emptyProtocolContext
  sent <- mapLeft show $
    checkProtocolAction
      (ProtocolSendRequest clientOld clientNext instanceRevision clientRole) clientContext
  received <- mapLeft show $
    checkProtocolAction
      (ProtocolReceiveRequest serverOld serverNext instanceRevision serverRole) serverContext
  assert (stepAction (checkedProtocolSessionStep sent) == SendAction)
    "production Core accepted a different client action"
  assert (stepAction (checkedProtocolSessionStep received) == ReceiveAction)
    "production Core accepted a different server action"
  exactSuccessor clientOld clientNext instanceRevision clientRole sent
  exactSuccessor serverOld serverNext instanceRevision serverRole received
  clientClosed <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest clientNext instanceRevision clientRole done)
    (checkedProtocolContext sent)
  serverClosed <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest serverNext instanceRevision serverRole done)
    (checkedProtocolContext received)
  assert (checkedProtocolSuccessor clientClosed == Nothing
       && checkedProtocolSuccessor serverClosed == Nothing)
    "terminal close invented a successor endpoint"
  assert (Map.null (protocolEndpoints (checkedProtocolContext clientClosed))
       && Map.null (protocolEndpoints (checkedProtocolContext serverClosed)))
    "source-derived local terminal paths retained protocol metadata"
  assert (Map.null (linearBindings (protocolResources (checkedProtocolContext clientClosed)))
       && Map.null (linearBindings (protocolResources (checkedProtocolContext serverClosed))))
    "source-derived terminal paths retained restricted endpoint owners"
  case checkProtocolAction
      (ProtocolSendRequest clientOld (Name "stale-again") instanceRevision clientRole)
      (checkedProtocolContext sent) of
    Left (ProtocolEndpointUnknown staleName) ->
      assert (staleName == clientOld) "stale error lost exact source predecessor identity"
    other -> Left ("consumed source predecessor was reusable: " <> show other)
  case checkProtocolAction
      (ProtocolReceiveRequest serverOld (Name "stale-again") instanceRevision serverRole)
      (checkedProtocolContext received) of
    Left (ProtocolEndpointUnknown staleName) ->
      assert (staleName == serverOld) "stale receive lost exact predecessor"
    other -> Left ("consumed source receive predecessor was reusable: " <> show other)

exactSuccessor
  :: Name -> Name -> ProtocolInstanceRevision -> ProtocolRoleKey
  -> CheckedProtocolStep -> Either String ()
exactSuccessor old next instanceRevision role checked = do
  binding <- maybe (Left "continuing action lost successor") Right
    (checkedProtocolSuccessor checked)
  assert (protocolEndpointName binding == next)
    "successor occurrence identity changed"
  assert (protocolEndpointSession binding == End done)
    "successor continuation head changed"
  assert (protocolEndpointInstance binding == instanceRevision
       && protocolEndpointRole binding == role)
    "successor protocol instance or role changed"
  let context = checkedProtocolContext checked
  assert (Map.notMember old (protocolEndpoints context)
       && Map.notMember old (linearBindings (protocolResources context)))
    "success left the predecessor live in a metadata/resource map"
  assert (Map.lookup next (linearBindings (protocolResources context))
       == Just (TyEndpoint (End done)))
    "successor Core resource binding disagreed with projected continuation"


-- Source-checked Ping binders and independently admitted projected heads
-- cannot derive protocol nominal authority from matching local Session text.
-- Both sides run mismatches and matching controls on original immutable states.
nominalSourcePingRejected :: Text.Text -> Either String ()
nominalSourcePingRejected source = do
  plans <- sourcePlans source
  let client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      revision = sourceProtocolInstance plans
      foreignRevision = ProtocolInstanceRevision "fsem02.foreign.ping.revision"
      foreignRole = ProtocolRoleKey "WrongPingRole"
  checkSide revision foreignRevision foreignRole clientOld clientNext
    clientRole (sourceClientHead plans) ProtocolSendRequest
  checkSide revision foreignRevision foreignRole serverOld serverNext
    serverRole (sourceServerHead plans) ProtocolReceiveRequest
  where
    checkSide :: ProtocolInstanceRevision -> ProtocolInstanceRevision
              -> ProtocolRoleKey -> Name -> Name -> ProtocolRoleKey
              -> Session
              -> (Name -> Name -> ProtocolInstanceRevision
                  -> ProtocolRoleKey -> ProtocolActionRequest)
              -> Either String ()
    checkSide revision foreignRevision foreignRole old next role headSession mkRequest = do
      wrongInstance <- mapLeft show $
        insertProtocolEndpoint old foreignRevision role headSession emptyProtocolContext
      wrongRole <- mapLeft show $
        insertProtocolEndpoint old revision foreignRole headSession emptyProtocolContext
      bothWrong <- mapLeft show $
        insertProtocolEndpoint old foreignRevision foreignRole headSession emptyProtocolContext
      matching <- mapLeft show $
        insertProtocolEndpoint old revision role headSession emptyProtocolContext
      let request = mkRequest old next revision role
      case checkProtocolAction request wrongInstance of
        Left (ProtocolInstanceMismatch name expected actual) ->
          assert (name == old && expected == revision && actual == foreignRevision)
            "Ping foreign instance error lost source endpoint or revision"
        other -> Left ("Ping foreign instance not rejected exactly: " <> show other)
      case checkProtocolAction request wrongRole of
        Left (ProtocolRoleMismatch name expected actual) ->
          assert (name == old && expected == role && actual == foreignRole)
            "Ping foreign role error lost source endpoint or role"
        other -> Left ("Ping foreign role not rejected exactly: " <> show other)
      case checkProtocolAction request bothWrong of
        Left (ProtocolInstanceMismatch name expected actual) ->
          assert (name == old && expected == revision && actual == foreignRevision)
            "Ping double mismatch did not prioritize nominal instance identity"
        other -> Left ("Ping double mismatch not rejected exactly: " <> show other)
      accepted <- mapLeft show $ checkProtocolAction request matching
      exactSuccessor old next revision role accepted
      let after = checkedProtocolContext accepted
      assert (Map.member old (protocolEndpoints matching)
              && Map.notMember next (protocolEndpoints matching)
              && Map.notMember old (protocolEndpoints after)
              && Map.member next (protocolEndpoints after))
        "nominal refusal or matching replay corrupted endpoint ownership"



-- A real source-derived Ping successor cannot shadow any of Γ/A/Δ, even
-- though only the predecessor is a protocol endpoint. Separately check the
-- metadata collision that is invisible to the structural resource maps.
-- Nominal instance, projection, and role are explicit admitted inputs.
sourcePingSuccessorResourceFreshness :: Text.Text -> Either String ()
sourcePingSuccessorResourceFreshness source = do
  plans <- sourcePlans source
  let client = sourceClientPlan plans
      server = sourceServerPlan plans
      revision = sourceProtocolInstance plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
  checkSide revision clientRole clientOld clientNext
    (sourceClientHead plans) ProtocolSendRequest
  checkSide revision serverRole serverOld serverNext
    (sourceServerHead plans) ProtocolReceiveRequest
  where
    checkSide
      :: ProtocolInstanceRevision -> ProtocolRoleKey -> Name -> Name
      -> Session
      -> (Name -> Name -> ProtocolInstanceRevision
          -> ProtocolRoleKey -> ProtocolActionRequest)
      -> Either String ()
    checkSide revision role old next headSession mkRequest = do
      let spectator = Name "fsem02.ping.borrowed.affine.spectator"
          request = mkRequest old next revision role
      assert (old /= next && spectator /= old && spectator /= next)
        "source identities unexpectedly alias borrowed spectator or successor"
      raw <- mapLeft show $
        insertProtocolEndpoint old revision role headSession emptyProtocolContext
      withSpectator <- mapLeft show $
        insertBinding Affine spectator (TyUInt 8) (protocolResources raw)
      withLoan <- mapLeft show $ startSharedLoan spectator withSpectator
      let initial = raw { protocolResources = withLoan }
      assert (Map.lookup spectator (affineBindings withLoan) == Just (TyUInt 8))
        "source spectator was not an affine owner"
      mapM_ (occupiedStructural initial request next) [Unrestricted, Affine, Linear]

      let fabricated = ProtocolEndpointBinding next revision role (End done)
          metadataCollision = initial
            { protocolEndpoints = Map.insert next fabricated (protocolEndpoints initial) }
      case checkProtocolAction request metadataCollision of
        Left (ProtocolEndpointMetadataConflict name) ->
          assert (name == next) "metadata-only collision lost successor name"
        other -> Left ("occupied metadata successor accepted: " <> show other)

      case checkProtocolAction (mkRequest old old revision role) initial of
        Left (ProtocolSessionError (SuccessorReusesEndpointName name)) ->
          assert (name == old) "same-name successor rejection lost predecessor"
        other -> Left ("source predecessor reused as successor: " <> show other)

      stepped <- mapLeft show $ checkProtocolAction request initial
      exactSuccessor old next revision role stepped
      let after = checkedProtocolContext stepped
          afterResources = protocolResources after
      assert (affineBindings afterResources == affineBindings withLoan
           && unrestrictedBindings afterResources == unrestrictedBindings withLoan
           && sharedLoans afterResources == sharedLoans withLoan
           && Map.member spectator (affineBindings afterResources))
        "send/receive changed unrelated borrowed affine owner, loan or Γ"
      case checkProtocolAction request after of
        Left (ProtocolEndpointUnknown name) ->
          assert (name == old) "stale source Ping predecessor lost occurrence"
        other -> Left ("consumed source Ping predecessor reused: " <> show other)

      closed <- mapLeft show $ checkProtocolAction
        (ProtocolCloseRequest next revision role done) after
      let afterClose = protocolResources (checkedProtocolContext closed)
      assert (affineBindings afterClose == affineBindings withLoan
           && sharedLoans afterClose == sharedLoans withLoan
           && Map.notMember next (linearBindings afterClose))
        "terminal Close changed borrowed spectator or retained successor"

    occupiedStructural
      :: ProtocolContext -> ProtocolActionRequest -> Name -> Mode -> Either String ()
    occupiedStructural initial request next mode = do
      occupied <- mapLeft show $
        insertBinding mode next (TyUInt 8) (protocolResources initial)
      let conflicting = initial { protocolResources = occupied }
      case checkProtocolAction request conflicting of
        Left (ProtocolSessionError (SessionResourceError (DuplicateBinding name))) ->
          assert (name == next) "structural collision error lost successor identity"
        other -> Left ("occupied " <> show mode <> " successor accepted or misdiagnosed: "
                   <> show other)

-- Complete parsed Ping controls, with independently supplied live nominal
-- metadata. Refusal never provides a successful successor or close result.
sourcePingCloseNominalGates :: Text.Text -> Either String ()
sourcePingCloseNominalGates source = do
  plans <- sourcePlans source
  let client = sourceClientPlan plans
      server = sourceServerPlan plans
      revision = sourceProtocolInstance plans
      foreignRevision = ProtocolInstanceRevision "fsem02.foreign.close.revision"
      foreignRole = ProtocolRoleKey "ForeignCloseRole"
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
  closeSide revision foreignRevision foreignRole clientRole
    clientOld clientNext (sourceClientHead plans) ProtocolSendRequest
  closeSide revision foreignRevision foreignRole serverRole
    serverOld serverNext (sourceServerHead plans) ProtocolReceiveRequest
  where
    closeSide
      :: ProtocolInstanceRevision -> ProtocolInstanceRevision -> ProtocolRoleKey
      -> ProtocolRoleKey -> Name -> Name -> Session
      -> (Name -> Name -> ProtocolInstanceRevision
          -> ProtocolRoleKey -> ProtocolActionRequest)
      -> Either String ()
    closeSide revision foreignRevision foreignRole role old next headSession mkRequest = do
      sourceContext <- mapLeft show $
        insertProtocolEndpoint old revision role headSession emptyProtocolContext
      sentOrReceived <- mapLeft show $
        checkProtocolAction (mkRequest old next revision role) sourceContext
      exactSuccessor old next revision role sentOrReceived
      let live = checkedProtocolContext sentOrReceived
          request = ProtocolCloseRequest next revision role done
          changeNominal instanceValue roleValue = live
            { protocolEndpoints = Map.adjust
                (\endpoint -> endpoint
                  { protocolEndpointInstance = instanceValue
                  , protocolEndpointRole = roleValue })
                next (protocolEndpoints live) }
          wrongInstance = changeNominal foreignRevision role
          wrongRole = changeNominal revision foreignRole
          bothWrong = changeNominal foreignRevision foreignRole
      assert (Map.lookup next (linearBindings (protocolResources wrongInstance))
                == Just (TyEndpoint (End done))
           && Map.member next (protocolEndpoints wrongInstance)
           && Map.notMember old (protocolEndpoints wrongInstance))
        "negative Close state must retain the real typed End successor"
      case checkProtocolAction request wrongInstance of
        Left (ProtocolInstanceMismatch name expected actual) ->
          assert (name == next && expected == revision && actual == foreignRevision)
            "Close wrong-instance diagnostic not exact"
        other -> Left ("Close foreign instance accepted or wrong error: " <> show other)
      case checkProtocolAction request wrongRole of
        Left (ProtocolRoleMismatch name expected actual) ->
          assert (name == next && expected == role && actual == foreignRole)
            "Close wrong-role diagnostic not exact"
        other -> Left ("Close foreign role accepted or wrong error: " <> show other)
      case checkProtocolAction request bothWrong of
        Left (ProtocolInstanceMismatch name expected actual) ->
          assert (name == next && expected == revision && actual == foreignRevision)
            "Close both-wrong did not prioritize instance mismatch"
        other -> Left ("Close both-wrong accepted or wrong error: " <> show other)
      closed <- mapLeft show $ checkProtocolAction request live
      assert (checkedProtocolPredecessor closed
              == ProtocolEndpointBinding next revision role (End done))
        "Close success did not consume the exact source-derived terminal binding"
      assert (checkedProtocolSuccessor closed == Nothing
           && Map.notMember next (protocolEndpoints (checkedProtocolContext closed))
           && Map.notMember next
                (linearBindings (protocolResources (checkedProtocolContext closed))))
        "Close success retained linear endpoint or invented a successor"
      case checkProtocolAction request (checkedProtocolContext closed) of
        Left (ProtocolEndpointUnknown name) ->
          assert (name == next) "stale Close rejection lost exact binder"
        other -> Left ("stale Close reused consumed endpoint: " <> show other)


-- The parsed Ping sides supply the actual source-resolved predecessor and
-- successor occurrences and independently checked projected local heads.
-- The active process population is a separate, explicitly admitted test
-- premise; no source syntax manufactures architectural authority.
sourcePingJointSuccessorAtomicity :: Text.Text -> Either String ()
sourcePingJointSuccessorAtomicity source = do
  plans <- sourcePlans source
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.joint.borrowed.server"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      runJoint = checkProcessCommunication (sourceBinaryInstance plans) network
  assert (sourceServerHead plans == dualSession (sourceClientHead plans))
    "source-projected Ping heads are not dual"
  assert (clientOld /= clientNext && serverOld /= serverNext
       && spectator /= clientOld && spectator /= clientNext
       && spectator /= serverOld && spectator /= serverNext)
    "source Ping endpoint occurrence unexpectedly aliases"
  rawClient <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  withSpectator <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  withLoan <- mapLeft show $ startSharedLoan spectator withSpectator
  let serverBefore = rawServer { protocolResources = withLoan }
      before = Map.fromList [(clientProcess, rawClient), (serverProcess, serverBefore)]
  -- A peer failure does not produce a one-sided successful context: the
  -- actual Core ProcessRendezvous checker returns an Either for the pair.
  mapM_ (rejectJointCollision runJoint request before clientProcess rawClient clientNext)
    [Unrestricted, Affine, Linear]
  mapM_ (rejectJointCollision runJoint request before serverProcess serverBefore serverNext)
    [Unrestricted, Affine, Linear]
  let ghost = ProtocolEndpointBinding serverNext revision serverRole (End done)
      badServer = serverBefore
        { protocolEndpoints = Map.insert serverNext ghost (protocolEndpoints serverBefore) }
  case runJoint (Map.insert serverProcess badServer before) request of
    Left (RendezvousProtocolError process (ProtocolEndpointMetadataConflict name)) ->
      assert (process == serverProcess && name == serverNext)
        "joint metadata-only collision lost peer process or successor name"
    other -> Left ("joint peer metadata collision incorrectly progressed: " <> show other)
  after <- mapLeft show $ runJoint before request
  clientAfter <- maybe (Left "joint success omitted client") Right (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "joint success omitted server") Right (Map.lookup serverProcess after)
  assert
    (Map.keysSet after == Map.keysSet before
     && Map.notMember clientOld (protocolEndpoints clientAfter)
     && Map.notMember serverOld (protocolEndpoints serverAfter)
     && Map.lookup clientNext (protocolEndpoints clientAfter)
       == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
     && Map.lookup serverNext (protocolEndpoints serverAfter)
       == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
     && Map.lookup clientNext (linearBindings (protocolResources clientAfter))
       == Just (TyEndpoint (End done))
     && Map.lookup serverNext (linearBindings (protocolResources serverAfter))
       == Just (TyEndpoint (End done))
     && Map.notMember clientOld (linearBindings (protocolResources clientAfter))
     && Map.notMember serverOld (linearBindings (protocolResources serverAfter)))
    "joint source Ping did not consume both predecessors and type both exact successors"
  assert
    (affineBindings (protocolResources serverAfter) == affineBindings withLoan
     && sharedLoans (protocolResources serverAfter) == sharedLoans withLoan
     && unrestrictedBindings (protocolResources serverAfter)
       == unrestrictedBindings withLoan)
    "joint transition changed borrowed server spectator or active loan"
  case runJoint after request of
    Left (RendezvousEndpointNotOwnedByProcess process stale) ->
      assert (process == clientProcess && stale == clientOld)
        "stale joint replay lost exact source client occurrence"
    other -> Left ("joint source Ping stale predecessor was reused: " <> show other)
  repeated <- mapLeft show $ runJoint before request
  assert (repeated == after && Map.lookup serverProcess before == Just serverBefore)
    "failed peer-side trials mutated the original joint source context"

rejectJointCollision
  :: (Map.Map ProcessKey ProtocolContext -> ProcessCommunicationAttempt
      -> Either ProcessRendezvousError (Map.Map ProcessKey ProtocolContext))
  -> ProcessCommunicationAttempt -> Map.Map ProcessKey ProtocolContext
  -> ProcessKey -> ProtocolContext -> Name -> Mode -> Either String ()
rejectJointCollision runJoint request before process context successor mode = do
  occupied <- mapLeft show $
    insertBinding mode successor (TyUInt 8) (protocolResources context)
  let bad = Map.insert process (context { protocolResources = occupied }) before
  case runJoint bad request of
    Left (RendezvousProtocolError actualProcess
      (ProtocolSessionError (SessionResourceError (DuplicateBinding name)))) ->
      assert (actualProcess == process && name == successor)
        "joint collision diagnostic lost exact process or source successor"
    other -> Left ("joint " <> show mode <> " collision yielded wrong result: " <> show other)

sourcePingJointNetwork :: Either String (ProcessNetwork, ProcessKey, ProcessKey)
sourcePingJointNetwork = do
  let root = InstanceKey "fsem02.ping.joint.root"
      clientSlot = OccurrenceSlotKey "client"
      serverSlot = OccurrenceSlotKey "server"
      leaf name = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration name
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren = []
        , architectureNodeReferences = []
        }
      spec = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration "root"
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren =
            [ ArchitectureChildSpec clientSlot (leaf "ClientWorker")
            , ArchitectureChildSpec serverSlot (leaf "ServerWorker") ]
        , architectureNodeReferences = []
        }
      clientSite = ProcessDeclarationSite
        (ProcessSiteKey "fsem02.ping.joint.client") (scopedInstanceKey root clientSlot)
      serverSite = ProcessDeclarationSite
        (ProcessSiteKey "fsem02.ping.joint.server") (scopedInstanceKey root serverSlot)
  graph <- mapLeft show $ instantiateArchitecture root spec
  network0 <- mapLeft show $ elaborateProcessNetwork graph [clientSite, serverSite]
  network <- mapLeft show $ activateRootProcesses network0
  let revision = identityInstanceRevision (processNetworkRoot network)
  pure (network, deriveProcessKey revision (processSiteKey clientSite),
        deriveProcessKey revision (processSiteKey serverSite))

sourcePingJointDeclaration :: Text.Text -> DeclarationIdentity
sourcePingJointDeclaration name = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation name []
  , declarationKey = DeclarationKey ("fsem02.ping.joint." <> name)
  , declarationInterfaceSemantics = SemanticAtom "fsem02.joint.external.interface"
  , declarationDefinitionSemantics = SemanticAtom "fsem02.joint.external.definition"
  }

sourceStaleCloseRejected :: Text.Text -> Either String ()
sourceStaleCloseRejected source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-stale-close" source)
  let components =
        [ c
        | Located _ top <- grammarV1TopLevelDecls parsed
        , GrammarV1ComponentDeclaration c <- [locatedValue (grammarV1Declaration top)]
        ]
  case components of
    (client : _) ->
      case grammarV1CheckedComponentSendClose
          (DeclarationKey "component.ClientWorker") client of
        Just (Left (GrammarV1ComponentSendCloseCloseMismatch expected actual)) ->
          assert
            (grammarV1ResolvedBinderDisplayName expected == "done"
             && grammarV1ResolvedBinderDisplayName actual == "endpoint")
            "source rejection did not identify successor versus consumed predecessor"
        other -> Left ("stale close source was not rejected exactly: " <> show other)
    _ -> Left "stale fixture did not parse a client component"

wrongSessionHeadRejected :: Text.Text -> Either String ()
wrongSessionHeadRejected source = do
  plans <- sourcePlans source
  let client = sourceClientPlan plans
      old = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      next = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      instanceRevision = sourceProtocolInstance plans
  context <- mapLeft show $
    insertProtocolEndpoint old instanceRevision clientRole
      (sourceClientHead plans) emptyProtocolContext
  case checkProtocolAction
      (ProtocolReceiveRequest old next instanceRevision clientRole) context of
    Left (ProtocolSessionError (UnexpectedSessionAction ReceiveAction actual)) ->
      assert (actual == sourceClientHead plans) "wrong session head diagnostic"
    other -> Left ("wrong session head bypassed the checker: " <> show other)

offerHeadAndMissingLabel :: Either String ()
offerHeadAndMissingLabel = do
  let current = Name "core.offer.before"
      next = Name "core.offer.after"
      offered = Offer
        [ Branch { branchLabel = "accept", branchPayload = Nothing
                 , branchContinuation = End done } ]
  context <- mapLeft show $
    insertProtocolEndpoint current suppliedInstance serverRole offered emptyProtocolContext
  accepted <- mapLeft show $
    checkProtocolAction
      (ProtocolOfferRequest current next suppliedInstance serverRole "accept") context
  exactSuccessor current next suppliedInstance serverRole accepted
  case checkProtocolAction
      (ProtocolOfferRequest current next suppliedInstance serverRole "missing") context of
    Left (ProtocolSessionError (UnknownSessionLabel label available)) ->
      assert (label == "missing" && available == ["accept"])
        "offer rejection lost requested/available labels"
    other -> Left ("missing offer label was not rejected exactly: " <> show other)

closeAndSelfSuccessorRejected :: Either String ()
closeAndSelfSuccessorRejected = do
  let old = Name "core.close.before"
  terminal <- mapLeft show $
    insertProtocolEndpoint old suppliedInstance clientRole (End done) emptyProtocolContext
  case checkProtocolAction
      (ProtocolCloseRequest old suppliedInstance clientRole (Outcome "wrong")) terminal of
    Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
      assert (expected == done && actual == Outcome "wrong")
        "close rejection lost the exact outcome pair"
    other -> Left ("wrong close outcome succeeded: " <> show other)
  initial <- mapLeft show $
    insertProtocolEndpoint old suppliedInstance clientRole
      (Send (Name "payload") (TyUInt 8) (End done)) emptyProtocolContext
  case checkProtocolAction
      (ProtocolSendRequest old old suppliedInstance clientRole) initial of
    Left (ProtocolSessionError (SuccessorReusesEndpointName actual)) ->
      assert (actual == old) "self-successor rejection lost predecessor identity"
    other -> Left ("self successor was not rejected exactly: " <> show other)

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

-- Only Core-only offer/negative fixtures use this explicitly supplied identity.
-- It is not inferred as nominal authority from source syntax.
suppliedInstance :: ProtocolInstanceRevision
suppliedInstance = ProtocolInstanceRevision "fsem02-core-only-explicit-instance"

done :: Outcome
done = Outcome "Done"

assert :: Bool -> String -> Either String ()
assert condition why = if condition then Right () else Left why

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
