{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Protocol
import Phil.Core.Protocol.Generic
import Phil.Core.Session (SessionError (..))
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-003 abstract endpoint transfers without exposing session shape" abstractTransferAccepts
    , test "PROT-003 transfer consumes predecessor and preserves exact contract" transferPreservesLinearity
    , test "PROT-003 every communication action rejects unconstrained session state" unconstrainedCommunicationRejects
    , test "PROT-003 transfer does not over-restrict concrete session use" concreteTransferStillCommunicates
    , test "PROT-003 transfer rejects a destination occurrence collision" destinationCollisionRejects
    , test "PROT-003 transfer rejects an unknown predecessor occurrence" unknownPredecessorRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

abstractTransferAccepts :: Either String ()
abstractTransferAccepts = do
  context <- abstractContext
  moved <- mapLeft show (transferProtocolEndpoint source destination context)
  binding <- maybe
    (Left "destination endpoint metadata missing after transfer")
    Right
    (lookupProtocolEndpoint destination moved)
  assert (protocolEndpointContract binding == abstractContract)
    "abstract transfer changed the endpoint contract"
  assert (protocolEndpointSession binding == abstractSession)
    "abstract transfer inspected or changed the session variable"

transferPreservesLinearity :: Either String ()
transferPreservesLinearity = do
  context <- abstractContext
  moved <- mapLeft show (transferProtocolEndpoint source destination context)
  assert (lookupProtocolEndpoint source moved == Nothing)
    "predecessor endpoint metadata survived transfer"
  assert (Map.notMember source (linearBindings (protocolResources moved)))
    "predecessor linear resource survived transfer"
  assert (Map.lookup destination (linearBindings (protocolResources moved)) == Just (TyEndpoint abstractSession))
    "successor linear resource did not preserve the abstract endpoint type"
  binding <- maybe
    (Left "successor endpoint metadata missing")
    Right
    (lookupProtocolEndpoint destination moved)
  assert (protocolEndpointContract binding == abstractContract)
    "successor endpoint contract changed during transfer"

unconstrainedCommunicationRejects :: Either String ()
unconstrainedCommunicationRejects = do
  context <- abstractContext
  mapM_ (expectUnconstrainedRejection context) communicationRequests

concreteTransferStillCommunicates :: Either String ()
concreteTransferStillCommunicates = do
  context <- mapLeft show $
    insertProtocolEndpoint source instanceRevision roleKey concreteSession emptyProtocolContext
  moved <- mapLeft show (transferProtocolEndpoint source destination context)
  step <- mapLeft show $
    checkProtocolAction
      (ProtocolSendRequest destination successor instanceRevision roleKey)
      moved
  binding <- maybe
    (Left "concrete send did not produce successor endpoint")
    Right
    (checkedProtocolSuccessor step)
  assert (protocolEndpointSession binding == End (Outcome "done"))
    "concrete successor session was not preserved after generic transfer"
  assert (protocolEndpointInstance binding == instanceRevision)
    "concrete successor lost protocol instance identity"
  assert (protocolEndpointRole binding == roleKey)
    "concrete successor lost protocol role identity"

destinationCollisionRejects :: Either String ()
destinationCollisionRejects = do
  first <- abstractContext
  context <- mapLeft show $
    insertProtocolEndpoint destination instanceRevision roleKey abstractSession first
  case transferProtocolEndpoint source destination context of
    Left (ProtocolEndpointMetadataConflict name) ->
      assert (name == destination) "wrong destination collision reported"
    other -> Left ("destination collision was not rejected exactly: " <> show other)

unknownPredecessorRejects :: Either String ()
unknownPredecessorRejects =
  case transferProtocolEndpoint (Name "missing") destination emptyProtocolContext of
    Left (ProtocolEndpointUnknown name) ->
      assert (name == Name "missing") "wrong unknown predecessor reported"
    other -> Left ("unknown predecessor was not rejected exactly: " <> show other)

expectUnconstrainedRejection
  :: ProtocolContext
  -> ProtocolActionRequest
  -> Either String ()
expectUnconstrainedRejection context request =
  case checkProtocolAction request context of
    Left (ProtocolSessionError (UnboundSessionVariable variable)) ->
      assert (variable == sessionVariable)
        ("wrong abstract session variable reported for " <> show request)
    other -> Left ("unconstrained communication was not rejected exactly for " <> show request <> ": " <> show other)

abstractContext :: Either String ProtocolContext
abstractContext = mapLeft show $
  insertProtocolEndpoint source instanceRevision roleKey abstractSession emptyProtocolContext

abstractContract :: ProtocolEndpointContract
abstractContract = ProtocolEndpointContract
  { protocolContractInstance = instanceRevision
  , protocolContractRole = roleKey
  , protocolContractSession = abstractSession
  }

communicationRequests :: [ProtocolActionRequest]
communicationRequests =
  [ ProtocolSendRequest source successor instanceRevision roleKey
  , ProtocolReceiveRequest source successor instanceRevision roleKey
  , ProtocolSelectRequest source successor instanceRevision roleKey "next"
  , ProtocolOfferRequest source successor instanceRevision roleKey "next"
  , ProtocolCloseRequest source instanceRevision roleKey (Outcome "done")
  ]

instanceRevision :: ProtocolInstanceRevision
instanceRevision = ProtocolInstanceRevision "protocol.generic.instance:v1"

roleKey :: ProtocolRoleKey
roleKey = ProtocolRoleKey "client"

sessionVariable :: Name
sessionVariable = Name "S"

abstractSession :: Session
abstractSession = SessionVar sessionVariable

concreteSession :: Session
concreteSession = Send (Name "payload") TyUnit (End (Outcome "done"))

source, destination, successor :: Name
source = Name "endpoint.in"
destination = Name "endpoint.forwarded"
successor = Name "endpoint.next"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
