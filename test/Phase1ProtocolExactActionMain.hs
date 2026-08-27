{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Protocol
import Phil.Core.Session
  ( SessionAction (..)
  , SessionError (..)
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-001 exact instance/role/state send is accepted" exactSendAccepted
    , test "PROT-001 wrong protocol instance is rejected" wrongInstanceRejected
    , test "PROT-001 wrong protocol role is rejected" wrongRoleRejected
    , test "PROT-001 action not admitted by current local state is rejected" wrongStateActionRejected
    , test "PROT-001 protocol metadata must agree with the live resource state" metadataStateMismatchRejected
    , test "PROT-001 exact labeled transition preserves provenance" exactSelectAccepted
    , test "PROT-001 unavailable label is rejected by the current state" wrongLabelRejected
    , test "PROT-001 exact terminal close consumes the endpoint with no successor" exactCloseAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactSendAccepted :: Either String ()
exactSendAccepted = do
  context <- fixture sendState
  checked <- mapLeft show $
    checkProtocolAction
      (ProtocolSendRequest endpoint successor protocolOne clientRole)
      context
  successorBinding <- maybe
    (Left "send produced no successor endpoint")
    Right
    (checkedProtocolSuccessor checked)
  assert (protocolEndpointInstance successorBinding == protocolOne)
    "successor lost exact protocol-instance identity"
  assert (protocolEndpointRole successorBinding == clientRole)
    "successor lost exact role identity"
  assert (protocolEndpointSession successorBinding == endState)
    "successor has the wrong local session state"
  let next = checkedProtocolContext checked
  assert (lookupProtocolEndpoint endpoint next == Nothing)
    "predecessor endpoint metadata survived successful transition"
  assert (lookupProtocolEndpoint successor next == Just successorBinding)
    "successor endpoint metadata was not installed"
  assert
    (Map.lookup successor (linearBindings (protocolResources next))
      == Just (TyEndpoint endState))
    "successor resource state disagrees with protocol metadata"

wrongInstanceRejected :: Either String ()
wrongInstanceRejected = do
  context <- fixture sendState
  case checkProtocolAction
      (ProtocolSendRequest endpoint successor protocolTwo clientRole)
      context of
    Left (ProtocolInstanceMismatch actualEndpoint expected actual) -> do
      assert (actualEndpoint == endpoint) "wrong endpoint in instance mismatch"
      assert (expected == protocolTwo) "wrong requested protocol instance in mismatch"
      assert (actual == protocolOne) "wrong live protocol instance in mismatch"
    other -> Left ("wrong protocol instance was not rejected exactly: " <> show other)

wrongRoleRejected :: Either String ()
wrongRoleRejected = do
  context <- fixture sendState
  case checkProtocolAction
      (ProtocolSendRequest endpoint successor protocolOne serverRole)
      context of
    Left (ProtocolRoleMismatch actualEndpoint expected actual) -> do
      assert (actualEndpoint == endpoint) "wrong endpoint in role mismatch"
      assert (expected == serverRole) "wrong requested role in mismatch"
      assert (actual == clientRole) "wrong live role in mismatch"
    other -> Left ("wrong protocol role was not rejected exactly: " <> show other)

wrongStateActionRejected :: Either String ()
wrongStateActionRejected = do
  context <- fixture sendState
  case checkProtocolAction
      (ProtocolReceiveRequest endpoint successor protocolOne clientRole)
      context of
    Left (ProtocolSessionError (UnexpectedSessionAction ReceiveAction actualState)) ->
      assert (actualState == sendState)
        "state checker reported the wrong current local session"
    other -> Left ("receive at a send state was not rejected exactly: " <> show other)

metadataStateMismatchRejected :: Either String ()
metadataStateMismatchRejected = do
  context <- fixture sendState
  let resources = protocolResources context
      corruptedResources = resources
        { linearBindings = Map.insert endpoint (TyEndpoint receiveState)
            (linearBindings resources)
        }
      corrupted = context { protocolResources = corruptedResources }
  case checkProtocolAction
      (ProtocolSendRequest endpoint successor protocolOne clientRole)
      corrupted of
    Left (ProtocolEndpointSessionMismatch actualEndpoint expected actual) -> do
      assert (actualEndpoint == endpoint) "wrong endpoint in state mismatch"
      assert (expected == sendState) "wrong protocol-metadata state in mismatch"
      assert (actual == receiveState) "wrong live-resource state in mismatch"
    other -> Left ("metadata/resource state drift was not rejected exactly: " <> show other)

exactSelectAccepted :: Either String ()
exactSelectAccepted = do
  context <- fixture selectState
  checked <- mapLeft show $
    checkProtocolAction
      (ProtocolSelectRequest endpoint successor protocolOne clientRole "accept")
      context
  successorBinding <- maybe
    (Left "select produced no successor endpoint")
    Right
    (checkedProtocolSuccessor checked)
  assert (protocolEndpointInstance successorBinding == protocolOne)
    "select successor changed protocol instance"
  assert (protocolEndpointRole successorBinding == clientRole)
    "select successor changed protocol role"
  assert (protocolEndpointSession successorBinding == endState)
    "select successor has the wrong branch continuation"

wrongLabelRejected :: Either String ()
wrongLabelRejected = do
  context <- fixture selectState
  case checkProtocolAction
      (ProtocolSelectRequest endpoint successor protocolOne clientRole "missing")
      context of
    Left (ProtocolSessionError (UnknownSessionLabel actual labels)) -> do
      assert (actual == "missing") "wrong missing label reported"
      assert (labels == ["accept", "retry"]) "wrong available label domain reported"
    other -> Left ("unavailable label was not rejected exactly: " <> show other)

exactCloseAccepted :: Either String ()
exactCloseAccepted = do
  context <- fixture endState
  checked <- mapLeft show $
    checkProtocolAction
      (ProtocolCloseRequest endpoint protocolOne clientRole okOutcome)
      context
  assert (checkedProtocolSuccessor checked == Nothing)
    "terminal close fabricated a successor endpoint"
  let next = checkedProtocolContext checked
  assert (lookupProtocolEndpoint endpoint next == Nothing)
    "closed endpoint metadata survived terminal consumption"
  assert (Map.notMember endpoint (linearBindings (protocolResources next)))
    "closed endpoint resource survived terminal consumption"

fixture :: Session -> Either String ProtocolContext
fixture session = mapLeft show $
  insertProtocolEndpoint endpoint protocolOne clientRole session emptyProtocolContext

protocolOne, protocolTwo :: ProtocolInstanceRevision
protocolOne = ProtocolInstanceRevision "phil.protocol.instance:upload:v1"
protocolTwo = ProtocolInstanceRevision "phil.protocol.instance:equal-shape-other:v1"

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "role:client"
serverRole = ProtocolRoleKey "role:server"

endpoint, successor :: Name
endpoint = Name "channel.current"
successor = Name "channel.next"

okOutcome :: Outcome
okOutcome = Outcome "ok"

endState :: Session
endState = End okOutcome

sendState :: Session
sendState = Send (Name "payload") (TyUInt 8) endState

receiveState :: Session
receiveState = Receive (Name "payload") (TyUInt 8) endState

selectState :: Session
selectState = Select
  [ Branch
      { branchLabel = "accept"
      , branchPayload = Nothing
      , branchContinuation = endState
      }
  , Branch
      { branchLabel = "retry"
      , branchPayload = Nothing
      , branchContinuation = sendState
      }
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
