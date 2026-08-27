{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Protocol
import Phil.Core.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROT-002 distinct instances may have equal local session syntax" equalShapeIsPossible
    , test "PROT-002 exact endpoint contract substitution accepts across occurrence names" exactSubstitutionAccepts
    , test "PROT-002 equal local shape does not permit cross-instance substitution" crossInstanceSubstitutionRejects
    , test "PROT-002 equal local shape does not permit cross-instance join" crossInstanceJoinRejects
    , test "PROT-002 same contract joins branch-local endpoint occurrences" exactJoinAccepts
    , test "PROT-002 equal local shape does not erase role identity" roleMismatchRejects
    , test "PROT-002 same instance and role still require exact local state" sessionMismatchRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

equalShapeIsPossible :: Either String ()
equalShapeIsPossible = do
  assert (protocolEndpointSession endpointA == protocolEndpointSession endpointB)
    "fixture local sessions are not definitionally equal"
  assert (protocolEndpointInstance endpointA /= protocolEndpointInstance endpointB)
    "fixture protocol instances unexpectedly coincide"
  assert (protocolEndpointContract endpointA /= protocolEndpointContract endpointB)
    "equal local session syntax collapsed distinct endpoint contracts"

exactSubstitutionAccepts :: Either String ()
exactSubstitutionAccepts =
  mapLeft show (checkProtocolEndpointSubstitution endpointA endpointAOtherName)

crossInstanceSubstitutionRejects :: Either String ()
crossInstanceSubstitutionRejects =
  case checkProtocolEndpointSubstitution endpointA endpointB of
    Left (ProtocolEndpointContractInstanceMismatch expected actual) -> do
      assert (expected == instanceA) "wrong expected protocol instance"
      assert (actual == instanceB) "wrong actual protocol instance"
    other -> Left ("cross-instance substitution was not rejected exactly: " <> show other)

crossInstanceJoinRejects :: Either String ()
crossInstanceJoinRejects =
  case checkProtocolEndpointJoin [endpointA, endpointB] of
    Left (ProtocolEndpointContractInstanceMismatch expected actual) -> do
      assert (expected == instanceA) "wrong expected protocol instance at join"
      assert (actual == instanceB) "wrong actual protocol instance at join"
    other -> Left ("cross-instance join was not rejected exactly: " <> show other)

exactJoinAccepts :: Either String ()
exactJoinAccepts = do
  contract <- mapLeft show (checkProtocolEndpointJoin [endpointA, endpointAOtherName])
  assert (contract == protocolEndpointContract endpointA)
    "exact join did not preserve the endpoint contract"
  assert (protocolEndpointName endpointA /= protocolEndpointName endpointAOtherName)
    "join fixture did not use distinct occurrence names"

roleMismatchRejects :: Either String ()
roleMismatchRejects =
  case checkProtocolEndpointSubstitution endpointA endpointWrongRole of
    Left (ProtocolEndpointContractRoleMismatch expected actual) -> do
      assert (expected == clientRole) "wrong expected role"
      assert (actual == serverRole) "wrong actual role"
    other -> Left ("role mismatch was not rejected exactly: " <> show other)

sessionMismatchRejects :: Either String ()
sessionMismatchRejects =
  case checkProtocolEndpointSubstitution endpointA endpointWrongSession of
    Left (ProtocolEndpointContractSessionMismatch expected actual) -> do
      assert (expected == sharedSession) "wrong expected session"
      assert (actual == successorSession) "wrong actual session"
    other -> Left ("session mismatch was not rejected exactly: " <> show other)

instanceA, instanceB :: ProtocolInstanceRevision
instanceA = ProtocolInstanceRevision "protocol.request-response.instance:a"
instanceB = ProtocolInstanceRevision "protocol.request-response.instance:b"

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "client"
serverRole = ProtocolRoleKey "server"

sharedSession :: Session
sharedSession = Send (Name "request") (TyUInt 32) successorSession

successorSession :: Session
successorSession = Receive (Name "response") (TyUInt 32) (End (Outcome "done"))

endpointA, endpointAOtherName, endpointB, endpointWrongRole, endpointWrongSession :: ProtocolEndpointBinding
endpointA = binding (Name "a.left") instanceA clientRole sharedSession
endpointAOtherName = binding (Name "a.right") instanceA clientRole sharedSession
endpointB = binding (Name "b.left") instanceB clientRole sharedSession
endpointWrongRole = binding (Name "a.server") instanceA serverRole sharedSession
endpointWrongSession = binding (Name "a.next") instanceA clientRole successorSession

binding :: Name -> ProtocolInstanceRevision -> ProtocolRoleKey -> Session -> ProtocolEndpointBinding
binding name instanceRevision role session = ProtocolEndpointBinding
  { protocolEndpointName = name
  , protocolEndpointInstance = instanceRevision
  , protocolEndpointRole = role
  , protocolEndpointSession = session
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
