{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Protocol
import Phil.Core.Session (SessionError (..))
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-005 successful action removes predecessor protocol metadata" predecessorMetadataRemoved
    , test "PROT-005 successful action removes predecessor linear resource" predecessorResourceRemoved
    , test "PROT-005 stale predecessor action rejects" stalePredecessorRejects
    , test "PROT-005 exact successor remains usable" successorRemainsUsable
    , test "PROT-005 similar successor shape does not revive predecessor" similarShapeDoesNotRevive
    , test "PROT-005 successor cannot reuse predecessor occurrence name" sameNameSuccessorRejects
    , test "PROT-005 terminal close consumes endpoint and stale close rejects" terminalCloseStaleRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

predecessorMetadataRemoved :: Either String ()
predecessorMetadataRemoved = do
  step <- firstStep
  let context = checkedProtocolContext step
  assert (Map.notMember endpoint0 (protocolEndpoints context))
    "consumed predecessor remained in protocol metadata"
  assert (Map.member endpoint1 (protocolEndpoints context))
    "exact successor missing from protocol metadata"

predecessorResourceRemoved :: Either String ()
predecessorResourceRemoved = do
  step <- firstStep
  let resources = protocolResources (checkedProtocolContext step)
  assert (Map.notMember endpoint0 (linearBindings resources))
    "consumed predecessor remained in linear resources"
  assert (Map.member endpoint1 (linearBindings resources))
    "exact successor missing from linear resources"

stalePredecessorRejects :: Either String ()
stalePredecessorRejects = do
  step <- firstStep
  case checkProtocolAction staleRequest (checkedProtocolContext step) of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == endpoint0) "stale rejection named the wrong predecessor"
    other -> Left ("stale predecessor action was not rejected exactly: " <> show other)

successorRemainsUsable :: Either String ()
successorRemainsUsable = do
  step <- firstStep
  second <- mapLeft show $
    checkProtocolAction secondRequest (checkedProtocolContext step)
  successor <- maybe
    (Left "second action failed to produce its exact successor")
    Right
    (checkedProtocolSuccessor second)
  assert (protocolEndpointName successor == endpoint2)
    "second action produced the wrong successor occurrence"
  assert (protocolEndpointSession successor == End doneOutcome)
    "second action produced the wrong successor session"
  assert (protocolEndpointInstance successor == protocolInstance)
    "successor lost protocol-instance identity"
  assert (protocolEndpointRole successor == clientRole)
    "successor lost role identity"

similarShapeDoesNotRevive :: Either String ()
similarShapeDoesNotRevive = do
  step <- firstStep
  successor <- maybe
    (Left "fixture did not produce a successor")
    Right
    (checkedProtocolSuccessor step)
  case protocolEndpointSession successor of
    Send {} -> pure ()
    other -> Left ("fixture successor was not structurally send-like: " <> show other)
  case checkProtocolAction staleRequest (checkedProtocolContext step) of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == endpoint0)
        "similar successor shape changed stale predecessor identity"
    other -> Left ("similar successor shape revived predecessor: " <> show other)

sameNameSuccessorRejects :: Either String ()
sameNameSuccessorRejects = do
  context <- initialContext
  let request = ProtocolSendRequest endpoint0 endpoint0 protocolInstance clientRole
  case checkProtocolAction request context of
    Left (ProtocolSessionError (SuccessorReusesEndpointName name)) ->
      assert (name == endpoint0) "same-name successor rejection named wrong endpoint"
    other -> Left ("same-name successor was not rejected exactly: " <> show other)

terminalCloseStaleRejects :: Either String ()
terminalCloseStaleRejects = do
  context <- mapLeft show $
    insertProtocolEndpoint closeEndpointName protocolInstance clientRole (End doneOutcome) emptyProtocolContext
  closed <- mapLeft show $
    checkProtocolAction
      (ProtocolCloseRequest closeEndpointName protocolInstance clientRole doneOutcome)
      context
  assert (checkedProtocolSuccessor closed == Nothing)
    "terminal close fabricated a successor"
  let closedContext = checkedProtocolContext closed
  assert (Map.notMember closeEndpointName (protocolEndpoints closedContext))
    "closed endpoint remained in protocol metadata"
  assert (Map.notMember closeEndpointName (linearBindings (protocolResources closedContext)))
    "closed endpoint remained in linear resources"
  case checkProtocolAction
      (ProtocolCloseRequest closeEndpointName protocolInstance clientRole doneOutcome)
      closedContext of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == closeEndpointName) "stale close rejection named wrong endpoint"
    other -> Left ("stale close was not rejected exactly: " <> show other)

firstStep :: Either String CheckedProtocolStep
firstStep = do
  context <- initialContext
  mapLeft show (checkProtocolAction firstRequest context)

initialContext :: Either String ProtocolContext
initialContext = mapLeft show $
  insertProtocolEndpoint endpoint0 protocolInstance clientRole initialSession emptyProtocolContext

firstRequest :: ProtocolActionRequest
firstRequest = ProtocolSendRequest endpoint0 endpoint1 protocolInstance clientRole

staleRequest :: ProtocolActionRequest
staleRequest = ProtocolSendRequest endpoint0 (Name "stale.successor") protocolInstance clientRole

secondRequest :: ProtocolActionRequest
secondRequest = ProtocolSendRequest endpoint1 endpoint2 protocolInstance clientRole

initialSession :: Session
initialSession = Send (Name "first") (TyUInt 32) successorSession

-- Same top-level communication shape as the predecessor, but a distinct live state.
successorSession :: Session
successorSession = Send (Name "second") (TyUInt 32) (End doneOutcome)

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.stale-reuse.instance:v1"

clientRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "client"

endpoint0, endpoint1, endpoint2, closeEndpointName :: Name
endpoint0 = Name "endpoint.0"
endpoint1 = Name "endpoint.1"
endpoint2 = Name "endpoint.2"
closeEndpointName = Name "endpoint.close"

doneOutcome :: Outcome
doneOutcome = Outcome "done"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
