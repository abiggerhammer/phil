{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: source-derived Ping heads + production Core.Protocol progression.
-- This checks finite witnesses, not universal Surface-to-Rocq refinement.
module Main (main) where

import Control.Monad (foldM)
import Data.List (permutations)
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
    , test "FSEM-02 parsed Ping joint predecessor resource agreement refuses either peer before continuation"
        (sourcePingJointPredecessorResourceGates accepted stale)
    , test "FSEM-02 parsed Ping missing process context precedes peer predecessor faults"
        (sourcePingJointMissingContextPrecedence accepted stale)
    , test "FSEM-02 Ping joint leaves a third activated process and its active loan untouched"
        (sourcePingJointThreeProcessFrame accepted stale)
    , test "FSEM-02 two disjoint source Ping pairs commute and refuse independently"
        (sourcePingDisjointPairCommutation accepted stale)
    , test "FSEM-02 disjoint Ping pairs complete all 24 terminal Close orders"
        (sourcePingDisjointTerminalInterleavings accepted stale)
    , test "FSEM-02 25920 partner terminal schedules, 144 partial prefixes, 288 stale cross-partner refusals"
        (sourcePingThreeDisjointTerminalSchedules accepted stale)
    , test "FSEM-02 competing Ping sends sharing a Client predecessor refuse second use"
        (sourcePingSharedClientContention accepted stale)
    , test "FSEM-02 competing Ping receivers sharing a Server predecessor refuse second use"
        (sourcePingSharedServerContention accepted stale)
    , test "FSEM-02 shared-Server winner Closes commute and loser remains stale"
        (sourcePingSharedServerTerminalCloseFrame accepted stale)
    , test "FSEM-02 shared-Client winner Closes commute and unselected Server stays live"
        (sourcePingSharedClientTerminalCloseFrame accepted stale)
    , test "FSEM-02 Ping joint validation orders nominal, projection and resource faults across peers"
        (sourcePingJointGatePriority accepted stale)
    , test "FSEM-02 source Ping joint nominal instance/role fail-closed peer"
        (sourcePingJointNominalRefusal accepted)
    , test "FSEM-02 source Ping joint terminal Close orders agree and reject stale replay"
        (sourcePingJointTerminalCloseDiamond accepted)
    , test "FSEM-02 source Ping half-Close peer nominal refusal keeps committed state and valid retry"
        (sourcePingJointCloseRefusalRetry accepted)
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


-- Both parser-checked Ping endpoints must retain their exact linear predecessor
-- resource at a synchronous Send/Receive. Adversarial Core resource-map faults
-- are deliberately NOT source permissions. No failed joint attempt commits
-- either peer's otherwise eligible successor.
sourcePingJointPredecessorResourceGates :: Text.Text -> Text.Text -> Either String ()
sourcePingJointPredecessorResourceGates accepted rejected = do
  -- Preserve the separate minimally rejected *source* witness and exact class.
  sourceStaleCloseRejected rejected
  plans <- sourcePlans accepted
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.ping.joint.resource.borrowed.spectator"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      run contexts = checkProcessCommunication (sourceBinaryInstance plans)
        network contexts request
  assert (sourceServerHead plans == dualSession (sourceClientHead plans)
       && clientOld /= clientNext && serverOld /= serverNext
       && clientOld /= serverOld && clientNext /= serverNext)
    "source Ping predecessor/successor heads are not exact independent duals"
  clientContext <- mapLeft show $
    insertProtocolEndpoint clientOld revision clientRole
      (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $
    insertProtocolEndpoint serverOld revision serverRole
      (sourceServerHead plans) emptyProtocolContext
  withSpectator <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  withLoan <- mapLeft show $ startSharedLoan spectator withSpectator
  let serverContext = rawServer { protocolResources = withLoan }
      before = Map.fromList [(clientProcess, clientContext), (serverProcess, serverContext)]
      changeResource owner replacement ctx =
        let resources = protocolResources ctx
            bindings = linearBindings resources
            changed = case replacement of
              Nothing -> Map.delete owner bindings
              Just ty -> Map.insert owner ty bindings
        in ctx { protocolResources = resources { linearBindings = changed } }
      probe process old headSession context = do
        let cases =
              [ ("missing", Nothing, ProtocolEndpointResourceMissing old)
              , ("wrong type", Just (TyUInt 8),
                  ProtocolEndpointResourceTypeMismatch old (TyUInt 8))
              , ("wrong session", Just (TyEndpoint (End done)),
                  ProtocolEndpointSessionMismatch old headSession (End done))
              ]
        mapM_ (\(label, replacement, expected) -> do
          let bad = Map.insert process (changeResource old replacement context) before
          case run bad of
            Left (RendezvousProtocolError actualProcess actualError) ->
              assert (actualProcess == process && actualError == expected)
                ("joint " <> label <> " error lost source predecessor/process or class")
            other -> Left ("joint " <> label <> " fault progressed or misdiagnosed: "
                            <> show other)) cases
  probe clientProcess clientOld (sourceClientHead plans) clientContext
  probe serverProcess serverOld (sourceServerHead plans) serverContext
  -- When both parties have faults, the real checker evaluates Client first.
  -- Repairing only Client exposes Server's fault, never a partial transition.
  let doubleFault = Map.insert clientProcess (changeResource clientOld Nothing clientContext)
                  $ Map.insert serverProcess
                      (changeResource serverOld (Just (TyUInt 8)) serverContext) before
  case run doubleFault of
    Left (RendezvousProtocolError process (ProtocolEndpointResourceMissing name)) ->
      assert (process == clientProcess && name == clientOld)
        "double-fault ordering did not refuse the client predecessor first"
    other -> Left ("double-fault Ping unexpectedly progressed: " <> show other)
  case run (Map.insert serverProcess
              (changeResource serverOld (Just (TyUInt 8)) serverContext) before) of
    Left (RendezvousProtocolError process
          (ProtocolEndpointResourceTypeMismatch name actual)) ->
      assert (process == serverProcess && name == serverOld && actual == TyUInt 8)
        "repairing Client did not expose Server's exact bad predecessor resource"
    other -> Left ("single remaining server fault unexpectedly progressed: " <> show other)
  after <- mapLeft show $ run before
  clientAfter <- maybe (Left "healthy Send missing Client") Right
    (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "healthy Receive missing Server") Right
    (Map.lookup serverProcess after)
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
    "restored joint Ping failed to consume both exact predecessors and type successors"
  assert
    (affineBindings (protocolResources serverAfter) == affineBindings withLoan
     && sharedLoans (protocolResources serverAfter) == sharedLoans withLoan)
    "resource-gated Ping changed unrelated borrowed affine spectator"
  again <- mapLeft show $ run before
  assert (again == after && Map.lookup clientProcess before == Just clientContext
         && Map.lookup serverProcess before == Just serverContext)
    "rejected resource trials silently mutated original joint source-derived state"
  case run after of
    Left (RendezvousEndpointNotOwnedByProcess process old) ->
      assert (process == clientProcess && old == clientOld)
        "replayed joint Ping did not reject its exact consumed predecessor"
    other -> Left ("stale joint Ping predecessor was reused after repair: " <> show other)


-- Missing process-local context precedes a malformed peer resource in the
-- actual production joint Send/Receive checker. These faults are external
-- test inputs, not source-granted resource edits or a synthetic rollback.
sourcePingJointMissingContextPrecedence :: Text.Text -> Text.Text -> Either String ()
sourcePingJointMissingContextPrecedence accepted rejected = do
  sourceStaleCloseRejected rejected
  plans <- sourcePlans accepted
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.ping.context.gate.spectator"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      run contexts = checkProcessCommunication (sourceBinaryInstance plans)
        network contexts request
      wrongResource name context =
        let resources = protocolResources context
        in context { protocolResources = resources
             { linearBindings = Map.insert name (TyUInt 8)
                 (linearBindings resources) } }
      expectError label expected contexts =
        case run contexts of
          Left actual -> assert (actual == expected)
            (label <> ": wrong exact process/error: " <> show actual)
          Right _ -> Left (label <> ": malformed joint context was accepted")
  assert (sourceServerHead plans == dualSession (sourceClientHead plans))
    "source Ping heads are not dual"
  clientContext <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  borrowed <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  loaned <- mapLeft show $ startSharedLoan spectator borrowed
  let serverContext = rawServer { protocolResources = loaned }
      before = Map.fromList [(clientProcess, clientContext),
                             (serverProcess, serverContext)]
      clientWrong = wrongResource clientOld clientContext
      serverWrong = wrongResource serverOld serverContext
      missingClientWrongServer = Map.singleton serverProcess serverWrong
      missingServerWrongClient = Map.singleton clientProcess clientWrong
  expectError "both process contexts missing"
    (RendezvousMissingProtocolContext clientProcess) Map.empty
  expectError "Client absent despite bad Server resource"
    (RendezvousMissingProtocolContext clientProcess) missingClientWrongServer
  expectError "Server absent despite bad Client resource"
    (RendezvousMissingProtocolContext serverProcess) missingServerWrongClient
  expectError "restoring Client exposes Server bad type"
    (RendezvousProtocolError serverProcess
       (ProtocolEndpointResourceTypeMismatch serverOld (TyUInt 8)))
    (Map.insert clientProcess clientContext missingClientWrongServer)
  expectError "restoring Server exposes Client bad type"
    (RendezvousProtocolError clientProcess
       (ProtocolEndpointResourceTypeMismatch clientOld (TyUInt 8)))
    (Map.insert serverProcess serverContext missingServerWrongClient)
  after <- mapLeft show $ run before
  clientAfter <- maybe (Left "joint context gate lost Client") Right
    (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "joint context gate lost Server") Right
    (Map.lookup serverProcess after)
  assert
    (Map.keysSet after == Map.keysSet before
      && Map.notMember clientOld (protocolEndpoints clientAfter)
      && Map.notMember serverOld (protocolEndpoints serverAfter)
      && Map.notMember clientOld (linearBindings (protocolResources clientAfter))
      && Map.notMember serverOld (linearBindings (protocolResources serverAfter))
      && Map.lookup clientNext (linearBindings (protocolResources clientAfter))
        == Just (TyEndpoint (End done))
      && Map.lookup serverNext (linearBindings (protocolResources serverAfter))
        == Just (TyEndpoint (End done))
      && Map.lookup clientNext (protocolEndpoints clientAfter)
        == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
      && Map.lookup serverNext (protocolEndpoints serverAfter)
        == Just (ProtocolEndpointBinding serverNext revision serverRole (End done)))
    "restored Ping did not consume both predecessors and install successors"
  assert
    (affineBindings (protocolResources serverAfter) == affineBindings loaned
      && sharedLoans (protocolResources serverAfter) == sharedLoans loaned
      && unrestrictedBindings (protocolResources serverAfter)
        == unrestrictedBindings loaned)
    "restored Ping changed independent borrowed affine spectator"
  duplicate <- mapLeft show $ run before
  assert (duplicate == after
    && Map.lookup clientProcess before == Just clientContext
    && Map.lookup serverProcess before == Just serverContext)
    "failed context/resource trials changed the original checked state"
  expectError "post-success stale predecessor"
    (RendezvousEndpointNotOwnedByProcess clientProcess clientOld) after


-- A new nonterminal diagnostic boundary: both endpoint nominal/projection
-- gates are checked before either process consumes linear predecessor state.
-- This is observable production checker order, not source-granted authority.
sourcePingJointGatePriority :: Text.Text -> Text.Text -> Either String ()
sourcePingJointGatePriority accepted rejected = do
  sourceStaleCloseRejected rejected
  plans <- sourcePlans accepted
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.ping.gate.priority.borrowed"
      foreignRevision = ProtocolInstanceRevision "fsem02.ping.gate.foreign"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      attempt left right = JointProcessRendezvous (SendReceiveRendezvous left right)
      normal = attempt clientSide serverSide
      run contexts request =
        checkProcessCommunication (sourceBinaryInstance plans) network contexts request
      corruptResource old context =
        let resources = protocolResources context
        in context { protocolResources = resources
          { linearBindings = Map.insert old (TyUInt 8) (linearBindings resources) } }
      corruptHead old context =
        context { protocolEndpoints = Map.adjust
          (\binding -> binding { protocolEndpointSession = End done })
          old (protocolEndpoints context) }
      expect label expected contexts request =
        case run contexts request of
          Left actual -> assert (actual == expected)
            (label <> ": unexpected exact diagnostic: " <> show actual)
          Right _ -> Left (label <> ": invalid two-party source Ping advanced")
  assert
    (foreignRevision /= revision && sourceServerHead plans == dualSession (sourceClientHead plans)
      && sourceClientHead plans /= End done && sourceServerHead plans /= End done)
    "Ping gate-priority test nominal and nonterminal session premises alias"
  clientContext <- mapLeft show $
    insertProtocolEndpoint clientOld revision clientRole
      (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $
    insertProtocolEndpoint serverOld revision serverRole
      (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let serverContext = rawServer { protocolResources = loaned }
      before = Map.fromList [(clientProcess, clientContext),
                             (serverProcess, serverContext)]
      badClient = corruptResource clientOld (corruptHead clientOld clientContext)
      badServer = corruptResource serverOld (corruptHead serverOld serverContext)
      nominalFailure process = RendezvousProtocolInstanceMismatch
        process revision foreignRevision
      headFailure process headSession = RendezvousProjectionSessionMismatch
        process headSession (End done)
      resourceFailure process old = RendezvousProtocolError process
        (ProtocolEndpointResourceTypeMismatch old (TyUInt 8))
      bothBadResources = Map.insert clientProcess
        (corruptResource clientOld clientContext)
        (Map.insert serverProcess (corruptResource serverOld serverContext) before)
  -- Requested nominal identity wins even over locally incorrect projection
  -- and incorrect linear resource on that same process.
  expect "Client foreign instance ahead of local head/resource"
    (nominalFailure clientProcess)
    (Map.insert clientProcess badClient before)
    (attempt (clientSide { rendezvousInstance = foreignRevision }) serverSide)
  expect "Server foreign instance ahead of local head/resource"
    (nominalFailure serverProcess)
    (Map.insert serverProcess badServer before)
    (attempt clientSide (serverSide { rendezvousInstance = foreignRevision }))
  -- Once nominal identity is restored, the projected Send/Receive head wins
  -- before resource lookup; restoring the exact head exposes the bad type.
  expect "Client projection before local linear resource"
    (headFailure clientProcess (sourceClientHead plans))
    (Map.insert clientProcess badClient before) normal
  expect "Server projection before local linear resource"
    (headFailure serverProcess (sourceServerHead plans))
    (Map.insert serverProcess badServer before) normal
  expect "Client restored head exposes bad linear resource"
    (resourceFailure clientProcess clientOld)
    (Map.insert clientProcess (corruptResource clientOld clientContext) before)
    normal
  expect "Server restored head exposes bad linear resource"
    (resourceFailure serverProcess serverOld)
    (Map.insert serverProcess (corruptResource serverOld serverContext) before)
    normal
  -- A fault in the later peer's nominal metadata is diagnosed BEFORE the
  -- earlier peer's linear-resource error: two-side validation is atomic.
  expect "Server nominal fault precedes Client resource fault"
    (nominalFailure serverProcess) bothBadResources
    (attempt clientSide (serverSide { rendezvousInstance = foreignRevision }))
  expect "after Server nominal repair, Client resource fault is first"
    (resourceFailure clientProcess clientOld) bothBadResources normal
  expect "after Client resource repair, Server resource fault remains"
    (resourceFailure serverProcess serverOld)
    (Map.insert serverProcess (corruptResource serverOld serverContext) before)
    normal
  after <- mapLeft show $ run before normal
  clientAfter <- maybe (Left "Ping priority success omitted Client") Right
    (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "Ping priority success omitted Server") Right
    (Map.lookup serverProcess after)
  assert
    (Map.notMember clientOld (protocolEndpoints clientAfter)
      && Map.notMember serverOld (protocolEndpoints serverAfter)
      && Map.lookup clientNext (protocolEndpoints clientAfter)
        == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
      && Map.lookup serverNext (protocolEndpoints serverAfter)
        == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
      && Map.notMember clientOld (linearBindings (protocolResources clientAfter))
      && Map.notMember serverOld (linearBindings (protocolResources serverAfter))
      && Map.lookup clientNext (linearBindings (protocolResources clientAfter))
        == Just (TyEndpoint (End done))
      && Map.lookup serverNext (linearBindings (protocolResources serverAfter))
        == Just (TyEndpoint (End done))
      && affineBindings (protocolResources serverAfter) == affineBindings loaned
      && sharedLoans (protocolResources serverAfter) == sharedLoans loaned)
    "restored joint Ping lost predecessor retirement, typed successors or borrowed frame"
  expect "post-success predecessor cannot replay"
    (RendezvousEndpointNotOwnedByProcess clientProcess clientOld) after normal
  assert (Map.lookup clientProcess before == Just clientContext
          && Map.lookup serverProcess before == Just serverContext
          && run before normal == Right after)
    "diagnostic probes changed original source-derived communication state"

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


-- A third independently activated process does not participate in the
-- source-derived binary Ping rendezvous. Its admitted process-local resource
-- context and active affine loan must survive both success and peer rejection.
-- This does NOT infer a third source component or activation resource authority.
sourcePingJointThreeProcessNetwork
  :: Either String (ProcessNetwork, ProcessKey, ProcessKey, ProcessKey)
sourcePingJointThreeProcessNetwork = do
  let root = InstanceKey "fsem02.ping.three.root"
      clientSlot = OccurrenceSlotKey "client"
      serverSlot = OccurrenceSlotKey "server"
      thirdSlot = OccurrenceSlotKey "uninvolved"
      leaf name = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration name
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren = []
        , architectureNodeReferences = []
        }
      spec = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration "three.root"
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren =
            [ ArchitectureChildSpec clientSlot (leaf "ClientWorker")
            , ArchitectureChildSpec serverSlot (leaf "ServerWorker")
            , ArchitectureChildSpec thirdSlot (leaf "ExternalUninvolvedWorker") ]
        , architectureNodeReferences = []
        }
      clientSite = ProcessDeclarationSite
        (ProcessSiteKey "fsem02.ping.three.client") (scopedInstanceKey root clientSlot)
      serverSite = ProcessDeclarationSite
        (ProcessSiteKey "fsem02.ping.three.server") (scopedInstanceKey root serverSlot)
      thirdSite = ProcessDeclarationSite
        (ProcessSiteKey "fsem02.ping.three.uninvolved") (scopedInstanceKey root thirdSlot)
  graph <- mapLeft show $ instantiateArchitecture root spec
  network0 <- mapLeft show $ elaborateProcessNetwork graph
    [clientSite, serverSite, thirdSite]
  network <- mapLeft show $ activateRootProcesses network0
  let revision = identityInstanceRevision (processNetworkRoot network)
      process site = deriveProcessKey revision (processSiteKey site)
  pure (network, process clientSite, process serverSite, process thirdSite)

sourcePingJointThreeProcessFrame :: Text.Text -> Text.Text -> Either String ()
sourcePingJointThreeProcessFrame source stale = do
  plans <- sourcePlans source
  -- Both source witnesses are real parser/checker input; the third process
  -- and its resource state are explicitly independent external premises.
  sourceStaleCloseRejected stale
  (network, clientProcess, serverProcess, thirdProcess) <-
    sourcePingJointThreeProcessNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.three.uninvolved.affine"
      clientSide = ProcessRendezvousSide
        clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide
        serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      runJoint = checkProcessCommunication (sourceBinaryInstance plans) network
  assert (clientProcess /= serverProcess && clientProcess /= thirdProcess
          && serverProcess /= thirdProcess)
    "three activated process identities unexpectedly alias"
  assert (sourceServerHead plans == dualSession (sourceClientHead plans))
    "three-process frame fixture lost source Ping duality"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  thirdResource <- mapLeft show $ insertBinding
    Affine spectator (TyUInt 8) (protocolResources emptyProtocolContext)
  thirdLoan <- mapLeft show $ startSharedLoan spectator thirdResource
  let thirdBefore = emptyProtocolContext { protocolResources = thirdLoan }
      before = Map.fromList
        [(clientProcess, clientBefore), (serverProcess, serverBefore),
         (thirdProcess, thirdBefore)]
      checkUninvolved label contexts =
        assert (Map.lookup thirdProcess contexts == Just thirdBefore
                && Map.keysSet contexts == Map.keysSet before)
          (label <> " lost exact uninvolved process/loan/context population")
  checkUninvolved "before" before
  -- An admitted pair progresses while the unrelated third activated process
  -- is preserved byte-for-byte, not just its affine owner projection.
  after <- mapLeft show $ runJoint before request
  checkUninvolved "after valid Ping" after
  clientAfter <- maybe (Left "missing three-process client") Right
    (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "missing three-process server") Right
    (Map.lookup serverProcess after)
  assert
    (Map.notMember clientOld (protocolEndpoints clientAfter)
     && Map.notMember serverOld (protocolEndpoints serverAfter)
     && Map.notMember clientOld (linearBindings (protocolResources clientAfter))
     && Map.notMember serverOld (linearBindings (protocolResources serverAfter))
     && Map.lookup clientNext (protocolEndpoints clientAfter)
          == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
     && Map.lookup serverNext (protocolEndpoints serverAfter)
          == Just (ProtocolEndpointBinding serverNext revision serverRole (End done)))
    "third-process frame success did not consume both source predecessors and type successors"
  -- Both malformed pre-states must refuse without producing ANY successful
  -- process map. Fixing only one independent peer restores the original
  -- admitted transition; no rollback or hidden repair is modeled.
  badClient <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (End done) emptyProtocolContext
  badServer <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (End done) emptyProtocolContext
  let malformedClient = Map.insert clientProcess badClient before
      malformedServer = Map.insert serverProcess badServer before
      checkRefusal label process expected contexts =
        case runJoint contexts request of
          Left (RendezvousProjectionSessionMismatch actual wanted observed) ->
            assert (actual == process && wanted == expected && observed == End done)
              (label <> " wrong process/head rejection")
          other -> Left (label <> " did not refuse with exact head error: " <> show other)
  checkUninvolved "bad client trial input" malformedClient
  checkUninvolved "bad server trial input" malformedServer
  checkRefusal "client invalid head" clientProcess (sourceClientHead plans)
    malformedClient
  checkRefusal "server invalid head" serverProcess (sourceServerHead plans)
    malformedServer
  assert (runJoint before request == Right after)
    "independently restored three-process input did not replay the exact successor"
  case runJoint after request of
    Left (RendezvousEndpointNotOwnedByProcess process staleName) ->
      assert (process == clientProcess && staleName == clientOld)
        "three-process stale predecessor refusal lost exact client process/name"
    other -> Left ("three-process stale rendezvous advanced: " <> show other)
  checkUninvolved "post-success stale refusal input" after


-- Two independent instances of the same source-checked Ping predecessor/
-- successor plan are externally instantiated at four distinct active sites.
-- This is a finite scheduler-order test, not source authority for a four-
-- component program or a universal partial-order reduction theorem.
sourcePingDisjointPairNetwork
  :: Either String (ProcessNetwork, ProcessKey, ProcessKey, ProcessKey, ProcessKey)
sourcePingDisjointPairNetwork = do
  let root = InstanceKey "fsem02.ping.disjoint.root"
      slotAC = OccurrenceSlotKey "a-client"
      slotAS = OccurrenceSlotKey "a-server"
      slotBC = OccurrenceSlotKey "b-client"
      slotBS = OccurrenceSlotKey "b-server"
      leaf name = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration name
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren = []
        , architectureNodeReferences = []
        }
      spec = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration "disjoint.root"
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren =
            [ ArchitectureChildSpec slotAC (leaf "ExternalClientA")
            , ArchitectureChildSpec slotAS (leaf "ExternalServerA")
            , ArchitectureChildSpec slotBC (leaf "ExternalClientB")
            , ArchitectureChildSpec slotBS (leaf "ExternalServerB") ]
        , architectureNodeReferences = []
        }
      site label slot = ProcessDeclarationSite (ProcessSiteKey label)
        (scopedInstanceKey root slot)
      acSite = site "fsem02.ping.disjoint.a.client" slotAC
      asSite = site "fsem02.ping.disjoint.a.server" slotAS
      bcSite = site "fsem02.ping.disjoint.b.client" slotBC
      bsSite = site "fsem02.ping.disjoint.b.server" slotBS
  graph <- mapLeft show $ instantiateArchitecture root spec
  network0 <- mapLeft show $ elaborateProcessNetwork graph
    [acSite, asSite, bcSite, bsSite]
  network <- mapLeft show $ activateRootProcesses network0
  let revision = identityInstanceRevision (processNetworkRoot network)
      process siteValue = deriveProcessKey revision (processSiteKey siteValue)
  pure (network, process acSite, process asSite, process bcSite, process bsSite)

sourcePingDisjointPairCommutation :: Text.Text -> Text.Text -> Either String ()
sourcePingDisjointPairCommutation accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, ac, as, bc, bs) <- sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      clientPlan = sourceClientPlan plans
      serverPlan = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint clientPlan)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor clientPlan)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint serverPlan)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor serverPlan)
      side process old next role = ProcessRendezvousSide
        process old next revision role
      joint c s = JointProcessRendezvous (SendReceiveRendezvous
        (side c clientOld clientNext clientRole)
        (side s serverOld serverNext serverRole))
      requestA = joint ac as
      requestB = joint bc bs
      run contexts request = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts request
      expectNext contexts process old next role = do
        context <- maybe (Left ("missing process context " <> show process))
          Right (Map.lookup process contexts)
        assert
          (Map.notMember old (protocolEndpoints context)
            && Map.notMember old (linearBindings (protocolResources context))
            && Map.lookup next (protocolEndpoints context)
              == Just (ProtocolEndpointBinding next revision role (End done))
            && Map.lookup next (linearBindings (protocolResources context))
              == Just (TyEndpoint (End done)))
          ("incorrect predecessor consumption or successor for " <> show process)
      expectStale label process old contexts request =
        case run contexts request of
          Left (RendezvousEndpointNotOwnedByProcess actual stale) ->
            assert (actual == process && stale == old)
              (label <> ": incorrect stale process/binder")
          other -> Left (label <> ": stale replay unexpectedly progressed: " <> show other)
      expectBadHead label process expected contexts request =
        case run contexts request of
          Left (RendezvousProjectionSessionMismatch actual wanted observed) ->
            assert (actual == process && wanted == expected && observed == End done)
              (label <> ": wrong exact projection-head refusal")
          other -> Left (label <> ": wrong nonterminal refusal: " <> show other)
  assert
    (length (Map.keys (Map.fromList [(ac, ()), (as, ()),
                                      (bc, ()), (bs, ())])) == 4
      && sourceServerHead plans == dualSession (sourceClientHead plans)
      && sourceClientHead plans /= End done
      && sourceServerHead plans /= End done)
    "two independently activated Ping pairs alias keys or heads"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  let before = Map.fromList
        [(ac, clientBefore), (as, serverBefore),
         (bc, clientBefore), (bs, serverBefore)]
  afterA <- mapLeft show $ run before requestA
  assert
    (Map.lookup bc afterA == Just clientBefore
      && Map.lookup bs afterA == Just serverBefore
      && Map.keysSet afterA == Map.keysSet before)
    "pair A mutated independent pair B or population"
  afterAB <- mapLeft show $ run afterA requestB
  afterB <- mapLeft show $ run before requestB
  assert
    (Map.lookup ac afterB == Just clientBefore
      && Map.lookup as afterB == Just serverBefore
      && Map.keysSet afterB == Map.keysSet before)
    "pair B mutated independent pair A or population"
  afterBA <- mapLeft show $ run afterB requestA
  assert (afterAB == afterBA && Map.keysSet afterAB == Map.keysSet before)
    "two distinct active Ping pairs did not commute under opposite schedules"
  expectNext afterAB ac clientOld clientNext clientRole
  expectNext afterAB as serverOld serverNext serverRole
  expectNext afterAB bc clientOld clientNext clientRole
  expectNext afterAB bs serverOld serverNext serverRole
  expectStale "stale pair A" ac clientOld afterAB requestA
  expectStale "stale pair B" bc clientOld afterAB requestB
  -- An independently malformed B head must neither abort the valid A step
  -- nor partially advance the B pair. Repair of B is explicit, not silent.
  wrongBServer <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (End done) emptyProtocolContext
  let brokenB = Map.insert bs wrongBServer before
  expectBadHead "B rejected before A" bs (sourceServerHead plans)
    brokenB requestB
  afterAWithBrokenB <- mapLeft show $ run brokenB requestA
  assert
    (Map.lookup bc afterAWithBrokenB == Just clientBefore
      && Map.lookup bs afterAWithBrokenB == Just wrongBServer
      && Map.keysSet afterAWithBrokenB == Map.keysSet before)
    "valid A step damaged independently malformed B contexts"
  expectBadHead "B still rejected after A" bs (sourceServerHead plans)
    afterAWithBrokenB requestB
  let repairedB = Map.insert bs serverBefore afterAWithBrokenB
  afterRepair <- mapLeft show $ run repairedB requestB
  assert (afterRepair == afterAB && run before requestA == Right afterA
          && run before requestB == Right afterB)
    "explicit B repair did not recover exact schedule-independent successor"
  expectStale "A after repaired B" ac clientOld afterRepair requestA
  expectStale "B after repaired B" bc clientOld afterRepair requestB


-- Two disjoint, externally activated source-checked Ping pairs: the two
-- rendezvous orders and all 24 four-End Close permutations converge. This
-- finite test never infers architecture/disposal authority from the source.
sourcePingDisjointTerminalInterleavings :: Text.Text -> Text.Text -> Either String ()
sourcePingDisjointTerminalInterleavings accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, ac, as, bc, bs) <- sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      sender = sourceClientPlan plans
      receiver = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint sender)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor sender)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint receiver)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor receiver)
      spectator = Name "fsem02.disjoint.terminal.loaned"
      side p old next role =
        ProcessRendezvousSide p old next revision role
      request client server = JointProcessRendezvous
        (SendReceiveRendezvous
          (side client clientOld clientNext clientRole)
          (side server serverOld serverNext serverRole))
      requestA = request ac as
      requestB = request bc bs
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      terminalSides =
        [(ac, clientNext, clientRole), (as, serverNext, serverRole),
         (bc, clientNext, clientRole), (bs, serverNext, serverRole)]
      closeOne contexts (p, endpoint, role) = do
        current <- maybe (Left "disjoint terminal Close missing process") Right
          (Map.lookup p contexts)
        step <- mapLeft show $ checkProtocolAction
          (ProtocolCloseRequest endpoint revision role done) current
        assert
          (checkedProtocolPredecessor step
             == ProtocolEndpointBinding endpoint revision role (End done)
           && checkedProtocolSuccessor step == Nothing)
          "disjoint terminal Close used the wrong typed End or made a successor"
        let closed = checkedProtocolContext step
        assert
          (Map.notMember endpoint (protocolEndpoints closed)
           && Map.notMember endpoint (linearBindings (protocolResources closed)))
          "disjoint terminal Close kept a consumed endpoint/linear owner"
        pure (Map.insert p closed contexts)
      expectStale label process contexts req =
        case run contexts req of
          Left (RendezvousEndpointNotOwnedByProcess actual old) ->
            assert (actual == process && old == clientOld)
              (label <> ": stale refusal lost the exact Client predecessor")
          other -> Left (label <> ": spent Ping request advanced: " <> show other)
  assert
    (sourceServerHead plans == dualSession (sourceClientHead plans)
     && clientOld /= clientNext && serverOld /= serverNext
     && length (Map.keys (Map.fromList
          [(ac, ()), (as, ()), (bc, ()), (bs, ())])) == 4)
    "disjoint terminal instances alias sites or protocol heads"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $ insertBinding Affine spectator
    (TyUInt 8) (protocolResources serverBefore)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let serverBBefore = serverBefore { protocolResources = loaned }
      before = Map.fromList
        [(ac, clientBefore), (as, serverBefore),
         (bc, clientBefore), (bs, serverBBefore)]
  afterA <- mapLeft show $ run before requestA
  afterAB <- mapLeft show $ run afterA requestB
  afterB <- mapLeft show $ run before requestB
  afterBA <- mapLeft show $ run afterB requestA
  assert
    (afterAB == afterBA && Map.keysSet afterAB == Map.keysSet before
     && Map.lookup bc afterA == Just clientBefore
     && Map.lookup bs afterA == Just serverBBefore
     && Map.lookup ac afterB == Just clientBefore
     && Map.lookup as afterB == Just serverBefore)
    "disjoint Ping first-step schedule mutated the other pair"
  mapM_ (\(p, endpoint, role) -> do
    current <- maybe (Left "missing typed End process") Right
      (Map.lookup p afterAB)
    assert
      (Map.lookup endpoint (protocolEndpoints current)
        == Just (ProtocolEndpointBinding endpoint revision role (End done))
       && Map.lookup endpoint (linearBindings (protocolResources current))
        == Just (TyEndpoint (End done)))
      ("disjoint progression lost exact End successor/owner " <> show p))
    terminalSides
  let schedules = permutations terminalSides
  assert (length schedules == 24)
    "four-End permutation enumeration is incomplete"
  outcomes <- mapM (foldM closeOne afterAB) schedules
  final <- case outcomes of
    [] -> Left "no disjoint Close schedules executed"
    first : rest -> do
      assert (all (== first) rest
           && Map.keysSet first == Map.keysSet before)
        "24 terminal Close interleavings differ or change process population"
      pure first
  mapM_ (\(p, endpoint, role) -> do
    current <- maybe (Left "missing disjoint final context") Right
      (Map.lookup p final)
    assert
      (Map.null (protocolEndpoints current)
       && Map.null (linearBindings (protocolResources current)))
      ("terminal Close retained a live endpoint/linear owner " <> show p)
    case checkProtocolAction
        (ProtocolCloseRequest endpoint revision role done) current of
      Left (ProtocolEndpointUnknown actual) ->
        assert (actual == endpoint)
          "repeated Close lost exact stale endpoint identity"
      other -> Left ("repeated Close unexpectedly advanced: " <> show other))
    terminalSides
  finalB <- maybe (Left "missing borrowed Server B") Right (Map.lookup bs final)
  assert
    (affineBindings (protocolResources finalB) == affineBindings loaned
     && sharedLoans (protocolResources finalB) == sharedLoans loaned)
    "terminal Close schedules lost active-loan affine spectator"
  expectStale "A terminal replay" ac final requestA
  expectStale "B terminal replay" bc final requestB
  -- A failed Close after one committed retirement is not a successor step.
  afterCloseA <- closeOne afterAB (ac, clientNext, clientRole)
  liveB <- maybe (Left "missing Server B after first Close") Right
    (Map.lookup bs afterCloseA)
  case checkProtocolAction
      (ProtocolCloseRequest serverNext revision serverRole (Outcome "Wrong"))
      liveB of
    Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
      assert (expected == done && actual == Outcome "Wrong")
        "half-closed wrong-outcome rejection lost its exact pair"
    other -> Left ("half-closed wrong-outcome Close advanced: " <> show other)
  expectStale "A after committed Close and refused B" ac afterCloseA requestA
  retried <- foldM closeOne afterCloseA
    [(bs, serverNext, serverRole), (as, serverNext, serverRole),
     (bc, clientNext, clientRole)]
  assert
    (retried == final && run before requestA == Right afterA
     && run before requestB == Right afterB)
    "refusal/retry differed from terminal result or deterministic replay"
  -- At each boundary of every four-End schedule, an invalid terminal
  -- outcome must reject without undoing a committed independent Close.
  -- Retired endpoints must refuse before checking the offered outcome.
  mapM_ (\schedule ->
    mapM_ (\prefixLength -> do
      prefix <- foldM closeOne afterAB (take prefixLength schedule)
      assert (Map.keysSet prefix == Map.keysSet afterAB)
        "Close-prefix fault injection changed process population"
      loanedServer <- maybe (Left "missing loaned server in Close prefix") Right
        (Map.lookup bs prefix)
      assert
        (affineBindings (protocolResources loanedServer) == affineBindings loaned
         && sharedLoans (protocolResources loanedServer) == sharedLoans loaned)
        "Close-prefix fault injection changed affine spectator"
      mapM_ (\(p, endpoint, role) -> do
        current <- maybe (Left "missing process at Close prefix") Right
          (Map.lookup p prefix)
        let badOutcome = Outcome "Wrong"
            attempted = checkProtocolAction
              (ProtocolCloseRequest endpoint revision role badOutcome) current
        case Map.lookup endpoint (protocolEndpoints current) of
          Nothing -> case attempted of
            Left (ProtocolEndpointUnknown actual) ->
              assert (actual == endpoint)
                "retired Close-prefix endpoint lost exact refusal identity"
            other -> Left ("retired Close-prefix endpoint was not refused: " <> show other)
          Just expectedEnd -> do
            assert
              (expectedEnd == ProtocolEndpointBinding endpoint revision role (End done))
              "live Close-prefix endpoint lost exact End successor"
            case attempted of
              Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
                assert (expected == done && actual == badOutcome)
                  "live Close-prefix wrong outcome lost exact diagnostic"
              other -> Left ("wrong-outcome Close-prefix attempt advanced: " <> show other)
        ) terminalSides
      expectStale "Close-prefix stale pair A" ac prefix requestA
      expectStale "Close-prefix stale pair B" bc prefix requestB
      resumed <- foldM closeOne prefix (drop prefixLength schedule)
      assert (resumed == final)
        "a refused Close-prefix probe changed the deterministic valid suffix"
      ) [0 .. length schedule]
    ) schedules

-- Non-normative boundary of disjoint-pair commutation: both requests
-- compete for exactly one source-derived Client linear predecessor.
sourcePingSharedClientContention :: Text.Text -> Text.Text -> Either String ()
sourcePingSharedClientContention accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, client, serverA, spectator, serverB) <- sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      clientPlan = sourceClientPlan plans
      serverPlan = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint clientPlan)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor clientPlan)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint serverPlan)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor serverPlan)
      spectatorName = Name "fsem02.shared-client.affine-spectator"
      side p old next role = ProcessRendezvousSide p old next revision role
      request server = JointProcessRendezvous (SendReceiveRendezvous
        (side client clientOld clientNext clientRole)
        (side server serverOld serverNext serverRole))
      requestA = request serverA
      requestB = request serverB
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      expectStale label contexts req =
        case run contexts req of
          Left (RendezvousEndpointNotOwnedByProcess actual old) ->
            assert (actual == client && old == clientOld)
              (label <> ": wrong shared Client or stale predecessor")
          other -> Left (label <> ": competing request progressed: " <> show other)
      checkFirst label after chosen untouched before serverBefore spectatorBefore = do
        c <- maybe (Left (label <> ": missing Client")) Right
          (Map.lookup client after)
        s <- maybe (Left (label <> ": missing Server")) Right
          (Map.lookup chosen after)
        assert
          (Map.keysSet after == Map.keysSet before
            && Map.notMember clientOld (protocolEndpoints c)
            && Map.notMember clientOld (linearBindings (protocolResources c))
            && Map.lookup clientNext (protocolEndpoints c)
              == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
            && Map.lookup clientNext (linearBindings (protocolResources c))
              == Just (TyEndpoint (End done))
            && Map.notMember serverOld (protocolEndpoints s)
            && Map.notMember serverOld (linearBindings (protocolResources s))
            && Map.lookup serverNext (protocolEndpoints s)
              == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
            && Map.lookup serverNext (linearBindings (protocolResources s))
              == Just (TyEndpoint (End done))
            && Map.lookup untouched after == Just serverBefore
            && Map.lookup spectator after == Just spectatorBefore)
          (label <> ": wrong typed successor or unrelated-state frame")
  assert
    (length (Map.keys (Map.fromList
      [(client, ()), (serverA, ()), (serverB, ()), (spectator, ())])) == 4
      && sourceServerHead plans == dualSession (sourceClientHead plans)
      && sourceClientHead plans /= End done
      && sourceServerHead plans /= End done)
    "shared Client test lost distinct activated keys or dual source heads"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  spectatorResource <- mapLeft show $ insertBinding Affine spectatorName
    (TyUInt 8) (protocolResources emptyProtocolContext)
  spectatorLoan <- mapLeft show $ startSharedLoan spectatorName spectatorResource
  let spectatorBefore = emptyProtocolContext { protocolResources = spectatorLoan }
      before = Map.fromList
        [(client, clientBefore), (serverA, serverBefore),
         (serverB, serverBefore), (spectator, spectatorBefore)]
  afterA <- mapLeft show $ run before requestA
  checkFirst "A first" afterA serverA serverB before serverBefore spectatorBefore
  expectStale "B after A" afterA requestB
  expectStale "A replay" afterA requestA
  afterB <- mapLeft show $ run before requestB
  checkFirst "B first" afterB serverB serverA before serverBefore spectatorBefore
  expectStale "A after B" afterB requestA
  expectStale "B replay" afterB requestB
  assert
    (afterA /= afterB && run before requestA == Right afterA
      && run before requestB == Right afterB
      && Map.lookup spectator afterA == Map.lookup spectator afterB)
    "overlap unexpectedly commuted or failed deterministic one-step replay"



-- Dual terminal boundary to shared-Server contention: one Client Send
-- predecessor competes with TWO externally activated Server Receives.
-- The winning Client and selected Server Close locally in either order.
-- The unselected Server's exact Receive head, its linear owner and a separate
-- actively loaned affine spectator must survive both Closes unchanged.
-- This test does not infer activation/disposal grants from source spelling.
sourcePingSharedClientTerminalCloseFrame
  :: Text.Text -> Text.Text -> Either String ()
sourcePingSharedClientTerminalCloseFrame accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, client, serverA, spectator, serverB) <-
    sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      sender = sourceClientPlan plans
      receiver = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint sender)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor sender)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint receiver)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor receiver)
      spectatorName = Name "fsem02.shared-client.terminal.loaned"
      side p old next role = ProcessRendezvousSide p old next revision role
      request server = JointProcessRendezvous (SendReceiveRendezvous
        (side client clientOld clientNext clientRole)
        (side server serverOld serverNext serverRole))
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      closeOne process endpoint role contexts = do
        current <- maybe (Left "shared-client Close missing process") Right
          (Map.lookup process contexts)
        step <- mapLeft show $ checkProtocolAction
          (ProtocolCloseRequest endpoint revision role done) current
        assert
          (checkedProtocolPredecessor step
            == ProtocolEndpointBinding endpoint revision role (End done)
           && checkedProtocolSuccessor step == Nothing)
          "shared-client Close failed to consume exact End without successor"
        let closed = checkedProtocolContext step
        assert (Map.notMember endpoint (protocolEndpoints closed)
             && Map.notMember endpoint (linearBindings (protocolResources closed)))
          "shared-client Close retained terminal endpoint or linear owner"
        pure (Map.insert process closed contexts)
      expectSpentClient label contexts req =
        case run contexts req of
          Left (RendezvousEndpointNotOwnedByProcess actual old) ->
            assert (actual == client && old == clientOld)
              (label <> ": wrong stale Client predecessor/diagnostic")
          other -> Left (label <> ": spent Client Send advanced: " <> show other)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans)
       && clientOld /= clientNext && serverOld /= serverNext
       && client /= serverA && client /= serverB && serverA /= serverB)
    "shared-client terminal test has aliased keys or nondual source heads"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $ insertBinding Affine spectatorName
    (TyUInt 8) (protocolResources emptyProtocolContext)
  loaned <- mapLeft show $ startSharedLoan spectatorName framed
  let spectatorBefore = emptyProtocolContext { protocolResources = loaned }
      before = Map.fromList
        [(client, clientBefore), (serverA, serverBefore),
         (serverB, serverBefore), (spectator, spectatorBefore)]
      finish label winner loser progressed = do
        clientEnd <- maybe (Left (label <> ": missing Client End")) Right
          (Map.lookup client progressed)
        winnerEnd <- maybe (Left (label <> ": missing Server End")) Right
          (Map.lookup winner progressed)
        assert
          (Map.lookup clientNext (protocolEndpoints clientEnd)
            == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
           && Map.lookup clientNext (linearBindings (protocolResources clientEnd))
            == Just (TyEndpoint (End done))
           && Map.lookup serverNext (protocolEndpoints winnerEnd)
            == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
           && Map.lookup serverNext (linearBindings (protocolResources winnerEnd))
            == Just (TyEndpoint (End done))
           && Map.notMember clientOld (protocolEndpoints clientEnd)
           && Map.notMember serverOld (protocolEndpoints winnerEnd)
           && Map.lookup loser progressed == Just serverBefore
           && Map.lookup spectator progressed == Just spectatorBefore)
          (label <> ": first step failed typed End or loser/spectator frame")
        -- A failed End action has no committed CheckedProtocolStep and cannot
        -- remove the still-live peer; the correct action remains available.
        case checkProtocolAction
            (ProtocolCloseRequest serverNext revision serverRole (Outcome "Wrong"))
            winnerEnd of
          Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
            assert (expected == done && actual == Outcome "Wrong")
              (label <> ": wrong terminal outcome did not reject precisely")
          other -> Left (label <> ": invalid terminal Close advanced: " <> show other)
        clientFirst <- closeOne client clientNext clientRole progressed
        forward <- closeOne winner serverNext serverRole clientFirst
        serverFirst <- closeOne winner serverNext serverRole progressed
        reversed <- closeOne client clientNext clientRole serverFirst
        assert
          (forward == reversed
           && Map.keysSet forward == Map.keysSet before
           && Map.lookup winner clientFirst == Just winnerEnd
           && Map.lookup client serverFirst == Just clientEnd
           && Map.lookup loser forward == Just serverBefore
           && Map.lookup spectator forward == Just spectatorBefore)
          (label <> ": local Close order changed loser/spectator or terminal map")
        let finalClient = Map.lookup client forward
            finalWinner = Map.lookup winner forward
        assert
          (maybe False (Map.null . protocolEndpoints) finalClient
           && maybe False (Map.null . protocolEndpoints) finalWinner
           && maybe False (Map.null . linearBindings . protocolResources) finalClient
           && maybe False (Map.null . linearBindings . protocolResources) finalWinner)
          (label <> ": committed terminal owners/endpoints remain live")
        expectSpentClient (label <> ": loser after both Closes")
          forward (request loser)
        expectSpentClient (label <> ": winner replay after both Closes")
          forward (request winner)
        case finalClient of
          Nothing -> Left (label <> ": missing final Client")
          Just ctx -> case checkProtocolAction
            (ProtocolCloseRequest clientNext revision clientRole done) ctx of
              Left (ProtocolEndpointUnknown old) ->
                assert (old == clientNext) (label <> ": stale Client Close identity")
              other -> Left (label <> ": repeated Client Close: " <> show other)
        case finalWinner of
          Nothing -> Left (label <> ": missing final Server")
          Just ctx -> case checkProtocolAction
            (ProtocolCloseRequest serverNext revision serverRole done) ctx of
              Left (ProtocolEndpointUnknown old) ->
                assert (old == serverNext) (label <> ": stale Server Close identity")
              other -> Left (label <> ": repeated Server Close: " <> show other)
        pure forward
  progressedA <- mapLeft show $ run before (request serverA)
  completedA <- finish "Server A wins" serverA serverB progressedA
  progressedB <- mapLeft show $ run before (request serverB)
  completedB <- finish "Server B wins" serverB serverA progressedB
  assert
    (completedA /= completedB
     && run before (request serverA) == Right progressedA
     && run before (request serverB) == Right progressedB
     && Map.lookup spectator completedA == Map.lookup spectator completedB)
    "shared-client alternate winners lacked deterministic replay or spectator frame"

-- Dual to shared-Client contention: independent source-derived Client senders
-- compete for the *same* Server process/linear Receive predecessor. The
-- source fixture grants neither the extra Client nor its activation.
sourcePingSharedServerContention :: Text.Text -> Text.Text -> Either String ()
sourcePingSharedServerContention accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, clientA, server, clientB, spectator) <- sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      clientPlan = sourceClientPlan plans
      serverPlan = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint clientPlan)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor clientPlan)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint serverPlan)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor serverPlan)
      spectatorName = Name "fsem02.shared-server.affine-spectator"
      side p old next role = ProcessRendezvousSide p old next revision role
      request client = JointProcessRendezvous (SendReceiveRendezvous
        (side client clientOld clientNext clientRole)
        (side server serverOld serverNext serverRole))
      requestA = request clientA
      requestB = request clientB
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      expectStale label expectedProcess expectedOld contexts req =
        case run contexts req of
          Left (RendezvousEndpointNotOwnedByProcess actual old) ->
            assert (actual == expectedProcess && old == expectedOld)
              (label <> ": wrong process or stale predecessor")
          other -> Left (label <> ": competing request progressed: " <> show other)
      checkFirst label after chosen untouched before clientBefore spectatorBefore = do
        c <- maybe (Left (label <> ": missing chosen Client")) Right
          (Map.lookup chosen after)
        s <- maybe (Left (label <> ": missing shared Server")) Right
          (Map.lookup server after)
        assert
          (Map.keysSet after == Map.keysSet before
            && Map.notMember clientOld (protocolEndpoints c)
            && Map.notMember clientOld (linearBindings (protocolResources c))
            && Map.lookup clientNext (protocolEndpoints c)
              == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
            && Map.lookup clientNext (linearBindings (protocolResources c))
              == Just (TyEndpoint (End done))
            && Map.notMember serverOld (protocolEndpoints s)
            && Map.notMember serverOld (linearBindings (protocolResources s))
            && Map.lookup serverNext (protocolEndpoints s)
              == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
            && Map.lookup serverNext (linearBindings (protocolResources s))
              == Just (TyEndpoint (End done))
            && Map.lookup untouched after == Just clientBefore
            && Map.lookup spectator after == Just spectatorBefore)
          (label <> ": wrong typed successor or unrelated-state frame")
  assert
    (length (Map.keys (Map.fromList
      [(clientA, ()), (server, ()), (clientB, ()), (spectator, ())])) == 4
      && sourceServerHead plans == dualSession (sourceClientHead plans)
      && sourceClientHead plans /= End done
      && sourceServerHead plans /= End done)
    "shared Server test lost distinct activated keys or dual source heads"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  spectatorResource <- mapLeft show $ insertBinding Affine spectatorName
    (TyUInt 8) (protocolResources emptyProtocolContext)
  spectatorLoan <- mapLeft show $ startSharedLoan spectatorName spectatorResource
  let spectatorBefore = emptyProtocolContext { protocolResources = spectatorLoan }
      before = Map.fromList
        [(clientA, clientBefore), (server, serverBefore),
         (clientB, clientBefore), (spectator, spectatorBefore)]
  afterA <- mapLeft show $ run before requestA
  checkFirst "A first" afterA clientA clientB before clientBefore spectatorBefore
  expectStale "B after A" server serverOld afterA requestB
  expectStale "A replay" clientA clientOld afterA requestA
  afterB <- mapLeft show $ run before requestB
  checkFirst "B first" afterB clientB clientA before clientBefore spectatorBefore
  expectStale "A after B" server serverOld afterB requestA
  expectStale "B replay" clientB clientOld afterB requestB
  -- Independent source-head corruption of the second sender has a precise
  -- projection failure and cannot consume the valid shared Server.
  badClientB <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (End done) emptyProtocolContext
  let brokenB = Map.insert clientB badClientB before
  case run brokenB requestB of
    Left (RendezvousProjectionSessionMismatch actual expected observed) ->
      assert (actual == clientB && expected == sourceClientHead plans
        && observed == End done) "malformed second Client had wrong rejection"
    other -> Left ("malformed second Client unexpectedly progressed: " <> show other)
  afterBrokenA <- mapLeft show $ run brokenB requestA
  assert (afterBrokenA == Map.insert clientB badClientB afterA
    && run before requestA == Right afterA
    && run before requestB == Right afterB
    && afterA /= afterB
    && Map.lookup spectator afterA == Map.lookup spectator afterB)
    "shared Server refused healthy first step, unexpectedly commuted or lost frame"


-- Distinct from the single-step shared-Server contention regression: advance
-- the winning Client and shared Server all the way to terminal Close.  Neither
-- local Close may revive the already consumed shared predecessor or mutate the
-- losing Client or an unrelated, actively borrowed affine spectator.  The
-- extra activated Client and disposal/nominal grants are external test inputs,
-- not architecture authority derived from the two-component Ping source.
sourcePingSharedServerTerminalCloseFrame
  :: Text.Text -> Text.Text -> Either String ()
sourcePingSharedServerTerminalCloseFrame accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  (network, clientA, server, clientB, spectator) <-
    sourcePingDisjointPairNetwork
  let revision = sourceProtocolInstance plans
      sender = sourceClientPlan plans
      receiver = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint sender)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor sender)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint receiver)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor receiver)
      spectatorName = Name "fsem02.shared-server.terminal.borrowed"
      side p old next role = ProcessRendezvousSide p old next revision role
      request client = JointProcessRendezvous (SendReceiveRendezvous
        (side client clientOld clientNext clientRole)
        (side server serverOld serverNext serverRole))
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      closeOne process endpoint role contexts = do
        current <- maybe (Left "terminal contention missing process") Right
          (Map.lookup process contexts)
        step <- mapLeft show $ checkProtocolAction
          (ProtocolCloseRequest endpoint revision role done) current
        assert (checkedProtocolPredecessor step
                   == ProtocolEndpointBinding endpoint revision role (End done)
             && checkedProtocolSuccessor step == Nothing)
          "terminal contention Close consumed wrong typed End or invented successor"
        let closed = checkedProtocolContext step
        assert (Map.notMember endpoint (protocolEndpoints closed)
             && Map.notMember endpoint (linearBindings (protocolResources closed)))
          "terminal contention Close retained endpoint or linear owner"
        pure (Map.insert process closed contexts)
      expectStale label expectedProcess old contexts req =
        case run contexts req of
          Left (RendezvousEndpointNotOwnedByProcess actual stale) ->
            assert (actual == expectedProcess && stale == old)
              (label <> ": wrong stale process/endpoint")
          other -> Left (label <> ": stale request progressed: " <> show other)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans)
       && clientOld /= clientNext && serverOld /= serverNext)
    "source Ping terminal contention heads or predecessors alias"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $ insertBinding Affine spectatorName
    (TyUInt 8) (protocolResources emptyProtocolContext)
  loaned <- mapLeft show $ startSharedLoan spectatorName framed
  let spectatorBefore = emptyProtocolContext { protocolResources = loaned }
      before = Map.fromList
        [(clientA, clientBefore), (server, serverBefore),
         (clientB, clientBefore), (spectator, spectatorBefore)]
      finish label winner loser progressed = do
        winnerEnd <- maybe (Left (label <> ": missing winner End")) Right
          (Map.lookup winner progressed)
        serverEnd <- maybe (Left (label <> ": missing server End")) Right
          (Map.lookup server progressed)
        assert
          (Map.lookup clientNext (protocolEndpoints winnerEnd)
             == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
           && Map.lookup serverNext (protocolEndpoints serverEnd)
             == Just (ProtocolEndpointBinding serverNext revision serverRole (End done))
           && Map.lookup loser progressed == Just clientBefore
           && Map.lookup spectator progressed == Just spectatorBefore)
          (label <> ": first step changed uninvolved Client or terminal heads")
        clientFirst <- closeOne winner clientNext clientRole progressed
        forward <- closeOne server serverNext serverRole clientFirst
        serverFirst <- closeOne server serverNext serverRole progressed
        reverseOrder <- closeOne winner clientNext clientRole serverFirst
        assert
          (forward == reverseOrder
           && Map.keysSet forward == Map.keysSet before
           && Map.lookup loser forward == Just clientBefore
           && Map.lookup spectator forward == Just spectatorBefore
           && Map.lookup server clientFirst == Just serverEnd
           && Map.lookup winner serverFirst == Just winnerEnd)
          (label <> ": terminal Close orders fail to commute or break frame")
        let finalWinner = Map.lookup winner forward
            finalServer = Map.lookup server forward
        assert
          (maybe False (Map.null . protocolEndpoints) finalWinner
           && maybe False (Map.null . protocolEndpoints) finalServer
           && maybe False
                (Map.null . linearBindings . protocolResources) finalWinner
           && maybe False
                (Map.null . linearBindings . protocolResources) finalServer)
          (label <> ": terminal endpoints or restricted owners remain")
        expectStale (label <> " loser after both Closes")
          server serverOld forward (request loser)
        expectStale (label <> " winner replay after both Closes")
          winner clientOld forward (request winner)
        case finalWinner of
          Nothing -> Left (label <> ": final winner missing")
          Just ctx -> case checkProtocolAction
            (ProtocolCloseRequest clientNext revision clientRole done) ctx of
              Left (ProtocolEndpointUnknown old) ->
                assert (old == clientNext) (label <> ": wrong stale Client Close")
              other -> Left (label <> ": repeated Client Close: " <> show other)
        case finalServer of
          Nothing -> Left (label <> ": final Server missing")
          Just ctx -> case checkProtocolAction
            (ProtocolCloseRequest serverNext revision serverRole done) ctx of
              Left (ProtocolEndpointUnknown old) ->
                assert (old == serverNext) (label <> ": wrong stale Server Close")
              other -> Left (label <> ": repeated Server Close: " <> show other)
        pure forward
  progressedA <- mapLeft show $ run before (request clientA)
  completedA <- finish "A wins" clientA clientB progressedA
  progressedB <- mapLeft show $ run before (request clientB)
  completedB <- finish "B wins" clientB clientA progressedB
  assert
    (completedA /= completedB
     && run before (request clientA) == Right progressedA
     && run before (request clientB) == Right progressedB
     && Map.lookup spectator completedA == Map.lookup spectator completedB)
    "alternate winner terminal replays were not deterministic or lost spectator"


sourcePingJointDeclaration :: Text.Text -> DeclarationIdentity
sourcePingJointDeclaration name = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation name []
  , declarationKey = DeclarationKey ("fsem02.ping.joint." <> name)
  , declarationInterfaceSemantics = SemanticAtom "fsem02.joint.external.interface"
  , declarationDefinitionSemantics = SemanticAtom "fsem02.joint.external.definition"
  }


-- A joint Core transition must refuse either peer's nominal metadata,
-- even if the other side is source-checked and locally ready.  The active
-- network and role/instance grants are externally supplied premises.
sourcePingJointNominalRefusal :: Text.Text -> Either String ()
sourcePingJointNominalRefusal source = do
  plans <- sourcePlans source
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      foreignRevision = ProtocolInstanceRevision "fsem02.joint.nominal.foreign"
      foreignRole = ProtocolRoleKey "Unassigned"
      spectator = Name "fsem02.joint.nominal.borrowed"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      attempt left right = JointProcessRendezvous (SendReceiveRendezvous left right)
      runJoint = checkProcessCommunication (sourceBinaryInstance plans) network
      good = attempt clientSide serverSide
      rejectInstance label process contexts request =
        case runJoint contexts request of
          Left (RendezvousProtocolInstanceMismatch actualProcess expected actual) ->
            assert (actualProcess == process && expected == revision
                    && actual == foreignRevision)
              (label <> ": instance mismatch lost exact process or revision")
          other -> Left (label <> ": expected exact joint instance rejection: " <> show other)
      rejectRole label process expectedRole actualRole contexts request =
        case runJoint contexts request of
          Left (RendezvousProtocolRoleMismatch actualProcess expected actual) ->
            assert (actualProcess == process && expected == expectedRole
                    && actual == actualRole)
              (label <> ": role mismatch lost exact process or roles")
          other -> Left (label <> ": expected exact joint role rejection: " <> show other)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans))
    "source Ping joint nominal heads are not dual"
  rawClient <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  borrowed <- mapLeft show $ startSharedLoan spectator framed
  let serverBefore = rawServer { protocolResources = borrowed }
      before = Map.fromList [(clientProcess, rawClient), (serverProcess, serverBefore)]
  assert (foreignRevision /= revision && foreignRole /= clientRole
          && foreignRole /= serverRole && clientOld /= clientNext
          && serverOld /= serverNext && spectator /= serverOld)
    "joint nominal test identities unexpectedly alias"

  rejectInstance "client requested instance" clientProcess before $
    attempt (clientSide { rendezvousInstance = foreignRevision }) serverSide
  rejectInstance "server requested instance" serverProcess before $
    attempt clientSide (serverSide { rendezvousInstance = foreignRevision })
  foreignClient <- mapLeft show $ insertProtocolEndpoint
    clientOld foreignRevision clientRole (sourceClientHead plans) emptyProtocolContext
  foreignServer <- mapLeft show $ insertProtocolEndpoint
    serverOld foreignRevision serverRole (sourceServerHead plans) emptyProtocolContext
  rejectInstance "client stored instance" clientProcess
    (Map.insert clientProcess foreignClient before) good
  rejectInstance "server stored instance" serverProcess
    (Map.insert serverProcess foreignServer before) good

  rejectRole "client requested role" clientProcess foreignRole clientRole before $
    attempt (clientSide { rendezvousRole = foreignRole }) serverSide
  rejectRole "server requested role" serverProcess foreignRole serverRole before $
    attempt clientSide (serverSide { rendezvousRole = foreignRole })
  foreignClientRole <- mapLeft show $ insertProtocolEndpoint
    clientOld revision foreignRole (sourceClientHead plans) emptyProtocolContext
  foreignServerRole <- mapLeft show $ insertProtocolEndpoint
    serverOld revision foreignRole (sourceServerHead plans) emptyProtocolContext
  rejectRole "client stored role" clientProcess clientRole foreignRole
    (Map.insert clientProcess foreignClientRole before) good
  rejectRole "server stored role" serverProcess serverRole foreignRole
    (Map.insert serverProcess foreignServerRole before) good

  -- Instance mismatch is diagnostic-first when both nominal fields differ.
  bothWrong <- mapLeft show $ insertProtocolEndpoint
    serverOld foreignRevision foreignRole (sourceServerHead plans) emptyProtocolContext
  let badPeer = Map.insert serverProcess bothWrong before
  rejectInstance "peer instance-before-role" serverProcess badPeer good
  assert (Map.lookup clientProcess badPeer == Just rawClient
          && runJoint badPeer good == runJoint badPeer good)
    "joint rejected peer unexpectedly changed client state"

  after <- mapLeft show $ runJoint before good
  clientAfter <- maybe (Left "nominal success omitted client") Right
    (Map.lookup clientProcess after)
  serverAfter <- maybe (Left "nominal success omitted server") Right
    (Map.lookup serverProcess after)
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
     && affineBindings (protocolResources serverAfter) == affineBindings borrowed
     && sharedLoans (protocolResources serverAfter) == sharedLoans borrowed)
    "joint matching nominal identity lost typed successors or loan frame"
  case runJoint after good of
    Left (RendezvousEndpointNotOwnedByProcess process name) ->
      assert (process == clientProcess && name == clientOld)
        "stale nominal joint replay lost original predecessor identity"
    other -> Left ("stale joint nominal replay unexpectedly progressed: " <> show other)


-- After a successful real two-process Ping rendezvous the source-derived
-- End endpoints may be closed in either order. This is commuting LOCAL
-- closure of distinct process contexts, not an invented atomic close or
-- a claim that source text itself grants process/disposal authority.
sourcePingJointTerminalCloseDiamond :: Text.Text -> Either String ()
sourcePingJointTerminalCloseDiamond source = do
  plans <- sourcePlans source
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.ping.close.diamond.borrowed"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      runJoint = checkProcessCommunication (sourceBinaryInstance plans) network
      closeOne process endpoint role contexts = do
        current <- maybe (Left "missing Ping close process") Right (Map.lookup process contexts)
        closed <- mapLeft show $
          checkProtocolAction (ProtocolCloseRequest endpoint revision role done) current
        assert (checkedProtocolPredecessor closed
                  == ProtocolEndpointBinding endpoint revision role (End done)
             && checkedProtocolSuccessor closed == Nothing)
          "Ping terminal close did not consume exact source successor without replacement"
        let next = checkedProtocolContext closed
        assert (Map.notMember endpoint (protocolEndpoints next)
             && Map.notMember endpoint (linearBindings (protocolResources next)))
          "Ping terminal close retained endpoint metadata or linear ownership"
        pure (Map.insert process next contexts)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans)
       && clientOld /= clientNext && serverOld /= serverNext)
    "Ping close-diamond source heads or endpoint identities are inconsistent"
  rawClient <- mapLeft show $
    insertProtocolEndpoint clientOld revision clientRole
      (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $
    insertProtocolEndpoint serverOld revision serverRole
      (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let before = Map.fromList
        [(clientProcess, rawClient),
         (serverProcess, rawServer { protocolResources = loaned })]
  progressed <- mapLeft show $ runJoint before request
  clientEnd <- maybe (Left "joint Ping omitted client End context") Right
    (Map.lookup clientProcess progressed)
  serverEnd <- maybe (Left "joint Ping omitted server End context") Right
    (Map.lookup serverProcess progressed)
  assert (Map.lookup clientNext (protocolEndpoints clientEnd)
            == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
       && Map.lookup serverNext (protocolEndpoints serverEnd)
            == Just (ProtocolEndpointBinding serverNext revision serverRole (End done)))
    "joint Ping did not establish both terminal heads before close"

  clientFirst <- closeOne clientProcess clientNext clientRole progressed
  forward <- closeOne serverProcess serverNext serverRole clientFirst
  serverFirst <- closeOne serverProcess serverNext serverRole progressed
  serverThenClient <- closeOne clientProcess clientNext clientRole serverFirst
  assert (forward == serverThenClient
       && Map.keysSet forward == Map.keysSet before
       && Map.lookup serverProcess clientFirst == Just serverEnd
       && Map.lookup clientProcess serverFirst == Just clientEnd)
    "independent source Ping Close orders changed the peer or final state"
  serverFinal <- maybe (Left "joint close omitted framed server") Right
    (Map.lookup serverProcess forward)
  assert (affineBindings (protocolResources serverFinal) == affineBindings loaned
       && sharedLoans (protocolResources serverFinal) == sharedLoans loaned
       && unrestrictedBindings (protocolResources serverFinal)
            == unrestrictedBindings loaned
       && Map.null (protocolEndpoints serverFinal)
       && Map.null (protocolEndpoints
            (maybe emptyProtocolContext id (Map.lookup clientProcess forward))))
    "Ping joint close lost spectator loan, or retained terminal endpoints"

  case checkProtocolAction
      (ProtocolCloseRequest clientNext revision clientRole (Outcome "Wrong"))
      clientEnd of
    Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
      assert (expected == done && actual == Outcome "Wrong")
        "wrong Close outcome lost exact expected/actual values"
    other -> Left ("wrong Ping joint terminal outcome was accepted: " <> show other)
  let foreignRole = ProtocolRoleKey "ForeignCloseRole"
  case checkProtocolAction
      (ProtocolCloseRequest serverNext revision foreignRole done) serverEnd of
    Left (ProtocolRoleMismatch name expected actual) ->
      assert (name == serverNext && expected == foreignRole && actual == serverRole)
        "wrong server Close role lost exact nominal identity"
    other -> Left ("wrong nominal Ping server Close was accepted: " <> show other)
  clientFinal <- maybe (Left "joint close omitted final client") Right
    (Map.lookup clientProcess forward)
  case checkProtocolAction
      (ProtocolCloseRequest clientNext revision clientRole done) clientFinal of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == clientNext) "stale client terminal replay lost source name"
    other -> Left ("stale client terminal Close was accepted: " <> show other)
  case checkProtocolAction
      (ProtocolCloseRequest serverNext revision serverRole done) serverFinal of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == serverNext) "stale server terminal replay lost source name"
    other -> Left ("stale server terminal Close was accepted: " <> show other)
  case runJoint forward request of
    Left (RendezvousEndpointNotOwnedByProcess process stale) ->
      assert (process == clientProcess && stale == clientOld)
        "post-close rendezvous replay lost consumed predecessor"
    other -> Left ("post-close stale Ping rendezvous progressed: " <> show other)

-- A failed local terminal Close is a rejected transition, not a partial
-- process commit. Replay correct source-derived Closes from the original
-- two-process state after exact nominal/head errors on either process.
-- The process population, protocol grants and disposal permission are
-- independently supplied premises, not inferred from the source spelling.
sourcePingJointCloseRefusalRetry :: Text.Text -> Either String ()
sourcePingJointCloseRefusalRetry source = do
  plans <- sourcePlans source
  (network, clientProcess, serverProcess) <- sourcePingJointNetwork
  let revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName (checkedComponentReceiveSuccessor server)
      spectator = Name "fsem02.ping.close.retry.borrowed"
      clientSide = ProcessRendezvousSide clientProcess clientOld clientNext revision clientRole
      serverSide = ProcessRendezvousSide serverProcess serverOld serverNext revision serverRole
      request = JointProcessRendezvous (SendReceiveRendezvous clientSide serverSide)
      foreignRevision = ProtocolInstanceRevision "fsem02.ping.close.retry.foreign"
      foreignRole = ProtocolRoleKey "fsem02.ping.close.retry.foreign.role"
      wrongOutcome = Outcome "RejectedCloseOutcome"
      closeOne process endpoint role contexts = do
        current <- maybe (Left "missing close retry process") Right
          (Map.lookup process contexts)
        checked <- mapLeft show $
          checkProtocolAction (ProtocolCloseRequest endpoint revision role done) current
        assert (checkedProtocolPredecessor checked
                  == ProtocolEndpointBinding endpoint revision role (End done)
               && checkedProtocolSuccessor checked == Nothing)
          "retry Close consumed wrong predecessor or invented a successor"
        pure (Map.insert process (checkedProtocolContext checked) contexts)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans))
    "source Ping retry heads are not exact duals"
  rawClient <- mapLeft show $
    insertProtocolEndpoint clientOld revision clientRole
      (sourceClientHead plans) emptyProtocolContext
  rawServer <- mapLeft show $
    insertProtocolEndpoint serverOld revision serverRole
      (sourceServerHead plans) emptyProtocolContext
  framed <- mapLeft show $
    insertBinding Affine spectator (TyUInt 8) (protocolResources rawServer)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let before = Map.fromList
        [(clientProcess, rawClient),
         (serverProcess, rawServer { protocolResources = loaned })]
  progressed <- mapLeft show $
    checkProcessCommunication (sourceBinaryInstance plans) network before request
  clientEnd <- maybe (Left "source Ping missing client terminal after rendezvous") Right
    (Map.lookup clientProcess progressed)
  serverEnd <- maybe (Left "source Ping missing server terminal after rendezvous") Right
    (Map.lookup serverProcess progressed)
  assert (Map.lookup clientNext (protocolEndpoints clientEnd)
            == Just (ProtocolEndpointBinding clientNext revision clientRole (End done))
       && Map.lookup serverNext (protocolEndpoints serverEnd)
            == Just (ProtocolEndpointBinding serverNext revision serverRole (End done)))
    "source Ping retry prestate lacks exact typed terminal successors"
  directClient <- closeOne clientProcess clientNext clientRole progressed
  directFinal <- closeOne serverProcess serverNext serverRole directClient
  reverseServer <- closeOne serverProcess serverNext serverRole progressed
  reverseFinal <- closeOne clientProcess clientNext clientRole reverseServer
  assert (directFinal == reverseFinal)
    "direct Ping two-process terminal closure orders disagree"
  let retry label process endpoint role peer peerEndpoint peerRole bad expected = do
        current <- maybe (Left "missing failed retry process") Right
          (Map.lookup process progressed)
        case checkProtocolAction bad current of
          Left observed ->
            assert (observed == expected)
              (label <> " wrong error: " <> show observed <> " /= " <> show expected)
          Right _ -> Left (label <> " was incorrectly accepted")
        -- Failed Either returns no CheckedProtocolStep: the original complete
        -- process map remains the only successor candidate for retry.
        repaired <- closeOne process endpoint role progressed
        assert (Map.lookup peer repaired == Map.lookup peer progressed)
          (label <> " touched an unrelated process on valid retry")
        completed <- closeOne peer peerEndpoint peerRole repaired
        assert (completed == directFinal)
          (label <> " refusal/retry differs from direct complete terminal state")
        serverResult <- maybe (Left "retry omitted server context") Right
          (Map.lookup serverProcess completed)
        assert (affineBindings (protocolResources serverResult) == affineBindings loaned
             && sharedLoans (protocolResources serverResult) == sharedLoans loaned
             && Map.null (protocolEndpoints serverResult))
          (label <> " did not preserve borrowed spectator or terminal retirement")
      checkClient = retry "client" clientProcess clientNext clientRole
                           serverProcess serverNext serverRole
      checkServer = retry "server" serverProcess serverNext serverRole
                           clientProcess clientNext clientRole
  checkClient (ProtocolCloseRequest clientNext foreignRevision clientRole done)
    (ProtocolInstanceMismatch clientNext foreignRevision revision)
  checkServer (ProtocolCloseRequest serverNext foreignRevision serverRole done)
    (ProtocolInstanceMismatch serverNext foreignRevision revision)
  checkClient (ProtocolCloseRequest clientNext revision foreignRole done)
    (ProtocolRoleMismatch clientNext foreignRole clientRole)
  checkServer (ProtocolCloseRequest serverNext revision foreignRole done)
    (ProtocolRoleMismatch serverNext foreignRole serverRole)
  checkClient (ProtocolCloseRequest clientNext revision clientRole wrongOutcome)
    (ProtocolSessionError (CloseOutcomeMismatch done wrongOutcome))
  checkServer (ProtocolCloseRequest serverNext revision serverRole wrongOutcome)
    (ProtocolSessionError (CloseOutcomeMismatch done wrongOutcome))
  -- Even when both nominal fields are wrong, exact instance rejection
  -- precedes role diagnosis. Neither side consumes the other endpoint.
  checkClient (ProtocolCloseRequest clientNext foreignRevision foreignRole done)
    (ProtocolInstanceMismatch clientNext foreignRevision revision)
  checkServer (ProtocolCloseRequest serverNext foreignRevision foreignRole done)
    (ProtocolInstanceMismatch serverNext foreignRevision revision)
  -- Two refused local Closes on opposite source-derived Ping participants
  -- leave BOTH original process contexts untouched, irrespective of order.
  -- A later valid Close is not a rollback of any previously committed action.
  let refuseWithoutCommit label process bad expected contexts = do
        current <- maybe (Left ("missing double-refusal " <> label)) Right
          (Map.lookup process contexts)
        case checkProtocolAction bad current of
          Left observed -> do
            assert (observed == expected)
              (label <> " double-refusal diagnostic: " <> show observed)
            pure contexts
          Right _ -> Left (label <> " unexpectedly committed a terminal Close")
      pairedRefusal label clientBad clientErr serverBad serverErr = do
        afterClient <- refuseWithoutCommit (label <> " client") clientProcess
          clientBad clientErr progressed
        afterServer <- refuseWithoutCommit (label <> " server") serverProcess
          serverBad serverErr afterClient
        firstServer <- refuseWithoutCommit (label <> " server-first") serverProcess
          serverBad serverErr progressed
        secondClient <- refuseWithoutCommit (label <> " client-second") clientProcess
          clientBad clientErr firstServer
        assert (afterServer == progressed && secondClient == progressed)
          (label <> " reordered refusals changed a peer or borrowed spectator")
        clientRetry <- closeOne clientProcess clientNext clientRole afterServer
        fullyRetried <- closeOne serverProcess serverNext serverRole clientRetry
        serverRetry <- closeOne serverProcess serverNext serverRole secondClient
        reversedRetry <- closeOne clientProcess clientNext clientRole serverRetry
        assert (fullyRetried == directFinal && reversedRetry == directFinal)
          (label <> " pair refusal then valid retries differ from direct closes")
        finalServer <- maybe (Left "double refusal lost final server") Right
          (Map.lookup serverProcess fullyRetried)
        assert (affineBindings (protocolResources finalServer) == affineBindings loaned
             && sharedLoans (protocolResources finalServer) == sharedLoans loaned)
          (label <> " double-refusal retry changed borrowed affine owner/loan")
  pairedRefusal "instance/role"
    (ProtocolCloseRequest clientNext foreignRevision clientRole done)
    (ProtocolInstanceMismatch clientNext foreignRevision revision)
    (ProtocolCloseRequest serverNext revision foreignRole done)
    (ProtocolRoleMismatch serverNext foreignRole serverRole)
  pairedRefusal "outcome/instance"
    (ProtocolCloseRequest clientNext revision clientRole wrongOutcome)
    (ProtocolSessionError (CloseOutcomeMismatch done wrongOutcome))
    (ProtocolCloseRequest serverNext foreignRevision serverRole done)
    (ProtocolInstanceMismatch serverNext foreignRevision revision)

  -- Mixed terminal outcome: one participant has ALREADY committed Close.
  -- A wrong-outcome attempt on the still-live peer is refused, with no
  -- rollback of the committed close and no loss of the borrow/loan frame.
  -- The retired participant cannot replay either its End successor or its
  -- already consumed source predecessor. Both close orders are exercised.
  let checkHalfClosed label halfClosed retired retiredEndpoint retiredOld
                      retiredRole peer peerEndpoint peerRole = do
        retiredState <- maybe (Left (label <> " missing retired process")) Right
          (Map.lookup retired halfClosed)
        peerState <- maybe (Left (label <> " missing live peer")) Right
          (Map.lookup peer halfClosed)
        assert (Map.notMember retiredEndpoint (protocolEndpoints retiredState)
             && Map.notMember retiredOld (protocolEndpoints retiredState)
             && Map.lookup peerEndpoint (protocolEndpoints peerState)
                 == Just (ProtocolEndpointBinding peerEndpoint revision peerRole (End done)))
          (label <> " committed Close unexpectedly removed the live peer")
        -- With a committed opposite Close, nominal instance/role failure
        -- must not disturb the still-live End peer. Instance precedence
        -- wins when both names are wrong; no failed request yields a step.
        let rejectNominalPeer name attemptedClose expected =
              case checkProtocolAction attemptedClose peerState of
                Left observed -> assert (observed == expected)
                  (label <> " " <> name <> " changed diagnostic: " <> show observed)
                Right _ -> Left (label <> " " <> name <> " advanced an inadmissible peer")
        rejectNominalPeer "foreign-instance"
          (ProtocolCloseRequest peerEndpoint foreignRevision peerRole done)
          (ProtocolInstanceMismatch peerEndpoint foreignRevision revision)
        rejectNominalPeer "foreign-role"
          (ProtocolCloseRequest peerEndpoint revision foreignRole done)
          (ProtocolRoleMismatch peerEndpoint foreignRole peerRole)
        rejectNominalPeer "both-foreign-instance-first"
          (ProtocolCloseRequest peerEndpoint foreignRevision foreignRole done)
          (ProtocolInstanceMismatch peerEndpoint foreignRevision revision)
        -- A refused peer Close has no CheckedProtocolStep to commit. The
        -- half-closed map remains the observable state for the valid retry.
        case checkProtocolAction
            (ProtocolCloseRequest peerEndpoint revision peerRole wrongOutcome)
            peerState of
          Left (ProtocolSessionError (CloseOutcomeMismatch expected actual)) ->
            assert (expected == done && actual == wrongOutcome)
              (label <> " failed peer Close lost exact outcome diagnostic")
          other -> Left (label <> " wrong-outcome peer Close: " <> show other)
        mapM_ (\staleEndpoint ->
          case checkProtocolAction
              (ProtocolCloseRequest staleEndpoint revision retiredRole done)
              retiredState of
            Left (ProtocolEndpointUnknown actual) ->
              assert (actual == staleEndpoint)
                (label <> " stale committed close replay lost endpoint identity")
            other -> Left (label <> " stale committed close unexpectedly advanced: "
                           <> show other))
          [retiredEndpoint, retiredOld]
        -- The absent predecessor check precedes even two invalid nominal
        -- fields: a retired endpoint never becomes live through a bad grant.
        case checkProtocolAction
            (ProtocolCloseRequest retiredEndpoint foreignRevision foreignRole done)
            retiredState of
          Left (ProtocolEndpointUnknown actual) ->
            assert (actual == retiredEndpoint)
              (label <> " stale endpoint did not take lookup precedence")
          other -> Left (label <> " stale nominal replay unexpectedly advanced: "
                         <> show other)
        assert (Map.lookup retired halfClosed == Just retiredState
             && Map.lookup peer halfClosed == Just peerState)
          (label <> " refused interleaving changed the committed prestate")
        afterRetry <- closeOne peer peerEndpoint peerRole halfClosed
        assert (afterRetry == directFinal)
          (label <> " refused peer retry rolled back first close or changed terminal map")
        finalServer <- maybe (Left (label <> " missing terminal server")) Right
          (Map.lookup serverProcess afterRetry)
        assert (affineBindings (protocolResources finalServer) == affineBindings loaned
             && sharedLoans (protocolResources finalServer) == sharedLoans loaned
             && Map.null (protocolEndpoints finalServer))
          (label <> " half-close/retry lost borrowed spectator or live peer endpoint")
  checkHalfClosed "client-committed/server-refused" directClient
    clientProcess clientNext clientOld clientRole
    serverProcess serverNext serverRole
  checkHalfClosed "server-committed/client-refused" reverseServer
    serverProcess serverNext serverOld serverRole
    clientProcess clientNext clientRole
  clientFinal <- maybe (Left "retry omitted final client context") Right
    (Map.lookup clientProcess directFinal)
  serverFinal <- maybe (Left "retry omitted final server context") Right
    (Map.lookup serverProcess directFinal)
  case checkProtocolAction
      (ProtocolCloseRequest clientNext revision clientRole done) clientFinal of
    Left (ProtocolEndpointUnknown endpoint) ->
      assert (endpoint == clientNext) "stale retry client lost original binder"
    other -> Left ("stale retry client advanced: " <> show other)
  case checkProtocolAction
      (ProtocolCloseRequest serverNext revision serverRole done) serverFinal of
    Left (ProtocolEndpointUnknown endpoint) ->
      assert (endpoint == serverNext) "stale retry server lost original binder"
    other -> Left ("stale retry server advanced: " <> show other)



-- Three disjoint, externally activated source-checked Ping pairs; neither
-- the three-pair architecture nor disposal authority comes from source.
sourcePingThreeDisjointTerminalSchedules :: Text.Text -> Text.Text -> Either String ()
sourcePingThreeDisjointTerminalSchedules accepted rejected = do
  plans <- sourcePlans accepted
  sourceStaleCloseRejected rejected
  let root = InstanceKey "fsem02.ping.triple.root"
      slotAC = OccurrenceSlotKey "a-client"
      slotAS = OccurrenceSlotKey "a-server"
      slotBC = OccurrenceSlotKey "b-client"
      slotBS = OccurrenceSlotKey "b-server"
      slotCC = OccurrenceSlotKey "c-client"
      slotCS = OccurrenceSlotKey "c-server"
      leaf label = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration label
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren = []
        , architectureNodeReferences = []
        }
      spec = ArchitectureNodeSpec
        { architectureNodeDeclaration = sourcePingJointDeclaration "triple.root"
        , architectureNodeStaticBindings = Map.empty
        , architectureNodeRequirements = []
        , architectureNodeChildren =
            [ ArchitectureChildSpec slotAC (leaf "ExternalClientA")
            , ArchitectureChildSpec slotAS (leaf "ExternalServerA")
            , ArchitectureChildSpec slotBC (leaf "ExternalClientB")
            , ArchitectureChildSpec slotBS (leaf "ExternalServerB")
            , ArchitectureChildSpec slotCC (leaf "ExternalClientC")
            , ArchitectureChildSpec slotCS (leaf "ExternalServerC") ]
        , architectureNodeReferences = []
        }
      site label slot = ProcessDeclarationSite (ProcessSiteKey label)
        (scopedInstanceKey root slot)
      acSite = site "fsem02.triple.a.client" slotAC
      asSite = site "fsem02.triple.a.server" slotAS
      bcSite = site "fsem02.triple.b.client" slotBC
      bsSite = site "fsem02.triple.b.server" slotBS
      ccSite = site "fsem02.triple.c.client" slotCC
      csSite = site "fsem02.triple.c.server" slotCS
  graph <- mapLeft show $ instantiateArchitecture root spec
  network0 <- mapLeft show $ elaborateProcessNetwork graph
    [acSite, asSite, bcSite, bsSite, ccSite, csSite]
  network <- mapLeft show $ activateRootProcesses network0
  let process siteValue = deriveProcessKey
        (identityInstanceRevision (processNetworkRoot network))
        (processSiteKey siteValue)
      ac = process acSite
      as = process asSite
      bc = process bcSite
      bs = process bsSite
      cc = process ccSite
      cs = process csSite
      revision = sourceProtocolInstance plans
      client = sourceClientPlan plans
      server = sourceServerPlan plans
      clientOld = grammarV1ResolvedBinderCoreName
        (checkedComponentSendEndpoint client)
      clientNext = grammarV1ResolvedBinderCoreName
        (checkedComponentSendSuccessor client)
      serverOld = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveEndpoint server)
      serverNext = grammarV1ResolvedBinderCoreName
        (checkedComponentReceiveSuccessor server)
      side p old next role =
        ProcessRendezvousSide p old next revision role
      request c s = JointProcessRendezvous (SendReceiveRendezvous
        (side c clientOld clientNext clientRole)
        (side s serverOld serverNext serverRole))
      requestA = request ac as
      requestB = request bc bs
      requestC = request cc cs
      run contexts req = checkProcessCommunication
        (sourceBinaryInstance plans) network contexts req
      terminalSides =
        [(ac, clientNext, clientRole), (as, serverNext, serverRole),
         (bc, clientNext, clientRole), (bs, serverNext, serverRole),
         (cc, clientNext, clientRole), (cs, serverNext, serverRole)]
      closeOne contexts (p, endpoint, role) = do
        current <- maybe (Left "triple terminal process absent") Right
          (Map.lookup p contexts)
        step <- mapLeft show $ checkProtocolAction
          (ProtocolCloseRequest endpoint revision role done) current
        assert
          (checkedProtocolPredecessor step
            == ProtocolEndpointBinding endpoint revision role (End done)
           && checkedProtocolSuccessor step == Nothing)
          "triple Close did not consume exact typed End predecessor"
        let closed = checkedProtocolContext step
        assert
          (Map.notMember endpoint (protocolEndpoints closed)
           && Map.notMember endpoint (linearBindings (protocolResources closed)))
          "triple Close retained endpoint/owner"
        pure (Map.insert p closed contexts)
  assert (sourceServerHead plans == dualSession (sourceClientHead plans)
       && clientOld /= clientNext && serverOld /= serverNext)
    "triple source Ping projection/occurrences changed"
  clientBefore <- mapLeft show $ insertProtocolEndpoint
    clientOld revision clientRole (sourceClientHead plans) emptyProtocolContext
  serverBefore <- mapLeft show $ insertProtocolEndpoint
    serverOld revision serverRole (sourceServerHead plans) emptyProtocolContext
  let spectator = Name "fsem02.triple.affine.loan"
  framed <- mapLeft show $ insertBinding Affine spectator
    (TyUInt 8) (protocolResources serverBefore)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let serverCBefore = serverBefore { protocolResources = loaned }
      before = Map.fromList
        [(ac, clientBefore), (as, serverBefore),
         (bc, clientBefore), (bs, serverBefore),
         (cc, clientBefore), (cs, serverCBefore)]
      rendezvousOrders = permutations [requestA, requestB, requestC]
      closeOrders = permutations terminalSides
      -- All Ping-before-Close schedules are already covered above.
      -- Here each pair may Close before unrelated pairs rendezvous.
      mixedEvents =
        [ (0 :: Int, True, Left requestA)
        , (1, True, Left requestB)
        , (2, True, Left requestC)
        , (0, False, Right (ac, clientNext, clientRole))
        , (0, False, Right (as, serverNext, serverRole))
        , (1, False, Right (bc, clientNext, clientRole))
        , (1, False, Right (bs, serverNext, serverRole))
        , (2, False, Right (cc, clientNext, clientRole))
        , (2, False, Right (cs, serverNext, serverRole)) ]
      legalMixed [] _ = True
      legalMixed ((pair, isPing, _) : remaining) started
        | isPing = pair `notElem` started && legalMixed remaining (pair : started)
        | otherwise = pair `elem` started && legalMixed remaining started
      mixedOrders = filter (\events -> legalMixed events []) (permutations mixedEvents)
  assert (Map.size before == 6 && length rendezvousOrders == 6
          && length closeOrders == 720)
    "triple Ping process collision or incomplete order census"
  canonical <- foldM (\contexts req -> mapLeft show (run contexts req))
    before [requestA, requestB, requestC]
  assert (Map.keysSet canonical == Map.keysSet before)
    "triple Ping changed externally activated process population"
  mapM_ (\(p, endpoint, role) -> do
    current <- maybe (Left "triple typed End missing") Right
      (Map.lookup p canonical)
    assert
      (Map.lookup endpoint (protocolEndpoints current)
        == Just (ProtocolEndpointBinding endpoint revision role (End done))
       && Map.lookup endpoint (linearBindings (protocolResources current))
        == Just (TyEndpoint (End done)))
      ("triple progression lost exact typed successor at " <> show p))
    terminalSides
  expected <- foldM closeOne canonical terminalSides
  -- External scheduler/instance authority selects a bijection; the source
  -- witness checks Send/Receive types, but does not fix participant pairing.
  -- All six typed partner choices must consume only the chosen two predecessors
  -- and converge to the same six-process terminal map. This is not a claim
  -- that source syntax provides architecture/partner-selection authority.
  let selectedServerOrders = permutations [as, bs, cs]
      selectedClientKeys = [ac, bc, cc]
      selectedRequests selectedServers =
        zipWith request selectedClientKeys selectedServers
      rejectConsumed label expectedProcess expectedEndpoint contexts attempted =
        case run contexts attempted of
          Left (RendezvousEndpointNotOwnedByProcess actualProcess predecessor) ->
            assert (actualProcess == expectedProcess && predecessor == expectedEndpoint)
              (label <> ": exact consumed owner diagnostic changed")
          other -> Left (label <> ": selected partner improperly reused: " <> show other)
  assert (length selectedServerOrders == 6)
    "three source-checked Ping partners lack all six external bijections"
  mapM_ (\selectedServers -> do
    let selected = selectedRequests selectedServers
        firstServer = head selectedServers
        freshServer = selectedServers !! 1
    firstState <- mapLeft show (run before (head selected))
    assert
      (Map.lookup bc firstState == Map.lookup bc before
        && Map.lookup cc firstState == Map.lookup cc before
        && Map.lookup freshServer firstState == Map.lookup freshServer before
        && Map.lookup (selectedServers !! 2) firstState
          == Map.lookup (selectedServers !! 2) before)
      "selected partner modified an unchosen Client/Server"
    rejectConsumed "selected Client with unchosen Server" ac clientOld
      firstState (request ac freshServer)
    rejectConsumed "unchosen Client with selected Server" firstServer serverOld
      firstState (request bc firstServer)
    replayed <- foldM (\contexts req -> mapLeft show (run contexts req))
      firstState (tail selected)
    assert (replayed == canonical)
      "retry after rejected partner rematching changed canonical endpoint owners"
    mapM_ (\selectedOrder -> do
      progressed <- foldM (\contexts req -> mapLeft show (run contexts req))
        before selectedOrder
      assert (progressed == canonical)
        "source-typed alternative partner order changed final joint successors"
      mapM_ (\closeOrder -> do
        terminal <- foldM closeOne progressed closeOrder
        assert (terminal == expected && Map.keysSet terminal == Map.keysSet before)
          "selected partner/terminal Close order changed final linear owners or spectator")
        closeOrders)
      (permutations selected))
    selectedServerOrders
  -- In addition to a complete externally chosen matching, exercise every
  -- prefix of every partner selection/order. Unmatched participants remain
  -- live and unchanged; no consumed peer may be rematched across that prefix.
  -- Failed cross-pair requests must not perturb valid suffix replay.
  mapM_ (\selectedServers -> do
    let chosenPairs = zip3 selectedClientKeys selectedServers
          (selectedRequests selectedServers)
    mapM_ (\chosenOrder ->
      mapM_ (\prefixLength -> do
        let committed = take prefixLength chosenOrder
            unmatched = drop prefixLength chosenOrder
        prefixState <- foldM
          (\contexts (_, _, req) -> mapLeft show (run contexts req))
          before committed
        mapM_ (\(freeClient, freeServer, _) ->
          assert
            (Map.lookup freeClient prefixState == Map.lookup freeClient before
             && Map.lookup freeServer prefixState == Map.lookup freeServer before)
            "partial external partner selection changed an unmatched source endpoint")
          unmatched
        mapM_ (\(spentClient, spentServer, _) -> do
          mapM_ (\(_, freeServer, _) ->
            rejectConsumed "partial-prefix spent Client with free Server"
              spentClient clientOld prefixState (request spentClient freeServer))
            unmatched
          mapM_ (\(freeClient, _, _) ->
            rejectConsumed "partial-prefix free Client with spent Server"
              spentServer serverOld prefixState (request freeClient spentServer))
            unmatched)
          committed
        spectatorContext <- maybe (Left "partial-prefix affine spectator missing") Right
          (Map.lookup cs prefixState)
        assert
          (affineBindings (protocolResources spectatorContext) == affineBindings loaned
           && sharedLoans (protocolResources spectatorContext) == sharedLoans loaned)
          "partial external partner selection altered the independent active loan"
        replayedPrefix <- foldM
          (\contexts (_, _, req) -> mapLeft show (run contexts req))
          prefixState unmatched
        assert
          (replayedPrefix == canonical
           && Map.keysSet replayedPrefix == Map.keysSet before)
          "partial-prefix rejected rematch changed valid suffix replay or owners")
        [0..3])
      (permutations chosenPairs))
    selectedServerOrders
  mapM_ (\order -> do
    progressed <- foldM (\contexts req -> mapLeft show (run contexts req))
      before order
    assert (progressed == canonical)
      "three independent Ping rendezvous do not commute"
    mapM_ (\closeOrder -> do
      result <- foldM closeOne progressed closeOrder
      assert (result == expected
           && Map.keysSet result == Map.keysSet before)
        "one of six rendezvous by 720 Close schedules differs")
      closeOrders)
    rendezvousOrders
  -- A Close before its own Ping cannot consume a live Send/Receive
  -- predecessor. Other pairs' committed Closes do not change that.
  let rejectPremature label contexts p endpoint role expectedHead = do
        current <- maybe (Left (label <> " missing process")) Right
          (Map.lookup p contexts)
        case checkProtocolAction
            (ProtocolCloseRequest endpoint revision role done) current of
          Left (ProtocolSessionError (UnexpectedSessionAction (CloseAction outcome) actual)) ->
            assert (outcome == done && actual == expectedHead)
              (label <> " lost exact attempted Close outcome or actual pre-Ping session head")
          other -> Left (label <> " incorrectly closed predecessor: " <> show other)
  rejectPremature "A Client initially" before ac clientOld clientRole (sourceClientHead plans)
  rejectPremature "B Server initially" before bs serverOld serverRole (sourceServerHead plans)
  onlyA <- mapLeft show (run before requestA)
  aClientClosed <- closeOne onlyA (ac, clientNext, clientRole)
  rejectPremature "B Client after A Close" aClientClosed
    bc clientOld clientRole (sourceClientHead plans)
  rejectPremature "C Server after A Close" aClientClosed
    cs serverOld serverRole (sourceServerHead plans)
  assert (length mixedOrders == 13440)
    "three-pair Ping-before-own-Close partial-order census changed"
  -- At every prefix of every legal schedule, interrogate every endpoint.
  -- Three distinct refusal classes depend on its *current* source-derived
  -- session phase. The rejected pure checker result cannot be used as a
  -- state transition; the same committed prefix must execute the valid suffix.
  let prefixSides =
        [(ac, clientOld, clientNext, clientRole, sourceClientHead plans),
         (as, serverOld, serverNext, serverRole, sourceServerHead plans),
         (bc, clientOld, clientNext, clientRole, sourceClientHead plans),
         (bs, serverOld, serverNext, serverRole, sourceServerHead plans),
         (cc, clientOld, clientNext, clientRole, sourceClientHead plans),
         (cs, serverOld, serverNext, serverRole, sourceServerHead plans)]
      invalidOutcome = Outcome "FSEM02.BadTerminal"
      pingPairs = [(requestA, ac, as), (requestB, bc, bs), (requestC, cc, cs)]
      inspectPrefix contexts = do
        mapM_ (inspectPhase contexts) prefixSides
        mapM_ (inspectStaleJointPing contexts) pingPairs
        framedProcess <- maybe (Left "mixed-prefix loaned process missing") Right
          (Map.lookup cs contexts)
        assert
          (affineBindings (protocolResources framedProcess) == affineBindings loaned
           && sharedLoans (protocolResources framedProcess) == sharedLoans loaned)
          "mixed-prefix fault probe changed independent affine spectator"
      inspectPhase contexts (processKey, predecessorName, successorName, endpointRole, prePingHead) = do
        current <- maybe (Left "mixed-prefix process context missing") Right
          (Map.lookup processKey contexts)
        let currentEndpoints = protocolEndpoints current
            currentOwners = linearBindings (protocolResources current)
            predecessorBinding = Map.lookup predecessorName currentEndpoints
            successorBinding = Map.lookup successorName currentEndpoints
        case (predecessorBinding, successorBinding) of
          (Just oldBinding, Nothing) -> do
            assert
              (oldBinding == ProtocolEndpointBinding predecessorName revision endpointRole prePingHead
               && Map.lookup predecessorName currentOwners == Just (TyEndpoint prePingHead)
               && Map.notMember successorName currentOwners)
              "mixed-prefix pre-Ping binding/linear owner mismatch"
            case checkProtocolAction
                (ProtocolCloseRequest predecessorName revision endpointRole done) current of
              Left (ProtocolSessionError (UnexpectedSessionAction (CloseAction attemptedOutcome) actualHead)) ->
                assert (attemptedOutcome == done && actualHead == prePingHead)
                  "mixed-prefix premature Close lost exact live Send/Receive head"
              other -> Left ("mixed-prefix premature Close wrong rejection: " <> show other)
          (Nothing, Just endBinding) -> do
            assert
              (endBinding == ProtocolEndpointBinding successorName revision endpointRole (End done)
               && Map.lookup successorName currentOwners == Just (TyEndpoint (End done))
               && Map.notMember predecessorName currentOwners)
              "mixed-prefix End successor/linear owner mismatch"
            case checkProtocolAction
                (ProtocolCloseRequest successorName revision endpointRole invalidOutcome) current of
              Left (ProtocolSessionError (CloseOutcomeMismatch expectedOutcome actualOutcome)) ->
                assert (expectedOutcome == done && actualOutcome == invalidOutcome)
                  "mixed-prefix wrong-outcome Close lost precise terminal mismatch"
              other -> Left ("mixed-prefix wrong-outcome Close wrong rejection: " <> show other)
          (Nothing, Nothing) -> do
            assert
              (Map.notMember predecessorName currentOwners
               && Map.notMember successorName currentOwners)
              "mixed-prefix retired endpoint retains a linear owner"
            case checkProtocolAction
                (ProtocolCloseRequest successorName revision endpointRole done) current of
              Left (ProtocolEndpointUnknown staleName) ->
                assert (staleName == successorName)
                  "mixed-prefix stale Close lost exact retired endpoint"
              other -> Left ("mixed-prefix stale Close wrong rejection: " <> show other)
          (Just _, Just _) ->
            Left "mixed-prefix predecessor and successor simultaneously live"
      -- At each mixed prefix, a whole-source-derived joint Ping already
      -- consumed by that pair must refuse its original two predecessors.
      -- No partial successor may appear even after unrelated committed Closes.
      inspectStaleJointPing contexts (requestValue, clientKey, serverKey) = do
        clientContext <- maybe (Left "stale Ping Client context missing") Right
          (Map.lookup clientKey contexts)
        serverContext <- maybe (Left "stale Ping Server context missing") Right
          (Map.lookup serverKey contexts)
        let clientLive = Map.member clientOld (protocolEndpoints clientContext)
            serverLive = Map.member serverOld (protocolEndpoints serverContext)
            clientOwners = linearBindings (protocolResources clientContext)
            serverOwners = linearBindings (protocolResources serverContext)
        case (clientLive, serverLive) of
          (True, True) ->
            assert
              (Map.lookup clientOld clientOwners == Just (TyEndpoint (sourceClientHead plans))
               && Map.lookup serverOld serverOwners == Just (TyEndpoint (sourceServerHead plans)))
              "mixed-prefix unstarted pair lost exact source-typed Ping predecessors"
          (False, False) -> do
            assert (Map.notMember clientOld clientOwners
                 && Map.notMember serverOld serverOwners)
              "mixed-prefix consumed Ping predecessor retains a linear owner"
            case run contexts requestValue of
              Left (RendezvousEndpointNotOwnedByProcess actualProcess old) ->
                assert (actualProcess == clientKey && old == clientOld)
                  "mixed-prefix stale joint Ping lost exact Client process/predecessor"
              other -> Left ("mixed-prefix stale joint Ping advanced or misclassified: "
                             <> show other)
          _ -> Left "mixed-prefix joint Ping consumed only one peer predecessor"
  mapM_ (\events -> do
    terminal <- foldM (\contexts (_, _, event) -> do
      inspectPrefix contexts
      case event of
        Left req -> mapLeft show (run contexts req)
        Right terminalSide -> closeOne contexts terminalSide) before events
    inspectPrefix terminal
    assert (terminal == expected && Map.keysSet terminal == Map.keysSet before)
      "mixed Ping/Close fault/retry schedule altered owned endpoint or affine frame")
    mixedOrders
  mapM_ (\(p, endpoint, role) -> do
    context <- maybe (Left "triple final process absent") Right
      (Map.lookup p expected)
    assert (Map.null (protocolEndpoints context)
         && Map.null (linearBindings (protocolResources context)))
      "triple terminal context retains endpoint owner"
    case checkProtocolAction
        (ProtocolCloseRequest endpoint revision role done) context of
      Left (ProtocolEndpointUnknown stale) ->
        assert (stale == endpoint) "triple stale Close changed endpoint identity"
      other -> Left ("triple stale Close unexpectedly succeeded: " <> show other))
    terminalSides
  finalLoaned <- maybe (Left "triple loaned server disappeared") Right
    (Map.lookup cs expected)
  assert (affineBindings (protocolResources finalLoaned) == affineBindings loaned
       && sharedLoans (protocolResources finalLoaned) == sharedLoans loaned)
    "triple schedules changed independent active affine loan"
  case run canonical requestA of
    Left (RendezvousEndpointNotOwnedByProcess p stale) ->
      assert (p == ac && stale == clientOld)
        "triple stale rendezvous returned wrong process/predecessor"
    other -> Left ("triple stale rendezvous advanced: " <> show other)
  serverC <- maybe (Left "triple Server C missing at End") Right
    (Map.lookup cs canonical)
  case checkProtocolAction
      (ProtocolCloseRequest serverNext revision serverRole (Outcome "Wrong"))
      serverC of
    Left (ProtocolSessionError (CloseOutcomeMismatch expectedOutcome actual)) ->
      assert (expectedOutcome == done && actual == Outcome "Wrong")
        "triple rejected wrong outcome with imprecise class"
    other -> Left ("triple wrong-outcome Close advanced: " <> show other)
  afterOne <- closeOne canonical (ac, clientNext, clientRole)
  retried <- foldM closeOne afterOne (tail terminalSides)
  assert (retried == expected)
    "triple refused Close prevented exact valid deterministic replay"

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
