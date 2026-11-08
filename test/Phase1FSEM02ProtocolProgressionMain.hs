{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: source-derived Ping heads + production Core.Protocol progression.
-- This checks finite witnesses, not universal Surface-to-Rocq refinement.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session
  ( SessionAction (..), SessionError (..), SessionStep (..) )
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Branch (..), Name (..), Outcome (..), Session (..), Ty (..))
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
    , test "FSEM-02 source stale close rejects with exact binder mismatch"
        (sourceStaleCloseRejected stale)
    , test "FSEM-02 mismatched session head rejects with precise action error"
        (wrongSessionHeadRejected accepted)
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
  { sourceClientPlan :: GrammarV1CheckedComponentSendClose
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
    { sourceClientPlan = clientPlan
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
