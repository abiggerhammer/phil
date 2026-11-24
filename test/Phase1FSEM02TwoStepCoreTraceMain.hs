{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE. Two sequential real Core.Protocol transitions.
-- The two-message protocol is separately instantiated here; the existing
-- accepted/rejected Grammar-v1 Ping source witnesses are independently tested.
-- This does NOT claim that Grammar-v1 admitted a combined two-send source.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionAction (..), SessionError (..), SessionStep (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Name (..), Outcome (..), Session (..), Ty (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  let cases =
        [ ("admitted two-generation Core Send/Receive consumes exact endpoints", twoStepTrace)
        ]
  results <- mapM (uncurry runCase) cases
  if and results then pure () else exitFailure

runCase :: String -> Either String () -> IO Bool
runCase label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

expect :: Bool -> String -> Either String ()
expect True _ = Right ()
expect False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

twoStepTrace :: Either String ()
twoStepTrace = do
  let client = ProtocolRoleKey "Client"
      server = ProtocolRoleKey "Server"
      first = Name "first"
      second = Name "second"
      done = Outcome "Done"
      instanceFamily = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = DeclarationKey "protocol.FSEM02TwoStepNative"
        , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.FSEM02TwoStepNative.v1"
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = client
        , protocolFamilyPeerRole = server
        , protocolFamilyPrimarySession =
            ProtocolTemplateSend first (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateSend second (ProtocolConcreteType (TyUInt 8))
                (ProtocolTemplateEnd done))
        }
      c0 = Name "client-initial"
      c1 = Name "client-intermediate"
      c2 = Name "client-terminal"
      s0 = Name "server-initial"
      s1 = Name "server-intermediate"
      s2 = Name "server-terminal"

  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy instanceFamily [] []
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue client
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue server
  let revision = binaryProtocolInstanceRevision instanceValue
      clientHead = protocolProjectionSession clientProjection
      serverHead = protocolProjectionSession serverProjection
      clientMiddle = Send second (TyUInt 8) (End done)
      serverMiddle = Receive second (TyUInt 8) (End done)
      cAction old next = ProtocolSendRequest old next revision client
      sAction old next = ProtocolReceiveRequest old next revision server
  expect (clientHead == Send first (TyUInt 8) clientMiddle
       && serverHead == Receive first (TyUInt 8) serverMiddle)
    "the independently instantiated protocol did not project exact dual two-step heads"
  clientBefore <- mapLeft show $
    insertProtocolEndpoint c0 revision client clientHead emptyProtocolContext
  serverBefore <- mapLeft show $
    insertProtocolEndpoint s0 revision server serverHead emptyProtocolContext
  clientFirst <- mapLeft show $ checkProtocolAction (cAction c0 c1) clientBefore
  serverFirst <- mapLeft show $ checkProtocolAction (sAction s0 s1) serverBefore
  let clientCommitted = checkedProtocolContext clientFirst
      serverCommitted = checkedProtocolContext serverFirst
  checkOne "client committed" clientCommitted c0 c1 clientMiddle revision client
  checkOne "server committed" serverCommitted s0 s1 serverMiddle revision server
  expect (stepAction (checkedProtocolSessionStep clientFirst) == SendAction
       && stepAction (checkedProtocolSessionStep serverFirst) == ReceiveAction)
    "first transitions were not Send and Receive"
  case checkProtocolAction (cAction c0 (Name "illegal-client")) clientCommitted of
    Left (ProtocolEndpointUnknown name) | name == c0 -> Right ()
    other -> Left ("consumed client predecessor not rejected exactly: " <> show other)
  case checkProtocolAction (sAction s0 (Name "illegal-server")) serverCommitted of
    Left (ProtocolEndpointUnknown name) | name == s0 -> Right ()
    other -> Left ("consumed server predecessor not rejected exactly: " <> show other)
  case checkProtocolAction
      (ProtocolReceiveRequest c1 (Name "wrong-action") revision client)
      clientCommitted of
    Left (ProtocolSessionError (UnexpectedSessionAction ReceiveAction _)) -> Right ()
    other -> Left ("wrong continuing session head not rejected: " <> show other)
  case checkProtocolAction
      (ProtocolSendRequest c1 (Name "wrong-role") revision server)
      clientCommitted of
    Left (ProtocolRoleMismatch name expected actual)
      | name == c1 && expected == server && actual == client -> Right ()
    other -> Left ("external role mismatch not rejected: " <> show other)
  -- Pure rejected probes must not alter either committed context.
  checkOne "client after refusals" clientCommitted c0 c1 clientMiddle revision client
  checkOne "server after refusals" serverCommitted s0 s1 serverMiddle revision server
  clientSecond <- mapLeft show $ checkProtocolAction (cAction c1 c2) clientCommitted
  serverSecond <- mapLeft show $ checkProtocolAction (sAction s1 s2) serverCommitted
  let clientFinal = checkedProtocolContext clientSecond
      serverFinal = checkedProtocolContext serverSecond
  checkOne "client final" clientFinal c1 c2 (End done) revision client
  checkOne "server final" serverFinal s1 s2 (End done) revision server
  expect (Map.notMember c0 (protocolEndpoints clientFinal)
       && Map.notMember s0 (protocolEndpoints serverFinal)
       && Map.notMember c0 (linearBindings (protocolResources clientFinal))
       && Map.notMember s0 (linearBindings (protocolResources serverFinal)))
    "second step resurrected first-generation predecessors"
  clientClosed <- mapLeft show $
    checkProtocolAction (ProtocolCloseRequest c2 revision client done) clientFinal
  serverClosed <- mapLeft show $
    checkProtocolAction (ProtocolCloseRequest s2 revision server done) serverFinal
  expect (Map.null (protocolEndpoints (checkedProtocolContext clientClosed))
       && Map.null (protocolEndpoints (checkedProtocolContext serverClosed))
       && Map.null (linearBindings (protocolResources (checkedProtocolContext clientClosed)))
       && Map.null (linearBindings (protocolResources (checkedProtocolContext serverClosed))))
    "terminal close left a live endpoint or linear resource"

checkOne :: String -> ProtocolContext -> Name -> Name -> Session
         -> ProtocolInstanceRevision -> ProtocolRoleKey -> Either String ()
checkOne label context old next expectedHead revision role = do
  expect (Map.size (protocolEndpoints context) == 1
       && Map.notMember old (protocolEndpoints context))
    (label <> ": wrong live protocol endpoint cardinality or old predecessor")
  expect (Map.size (linearBindings (protocolResources context)) == 1
       && Map.notMember old (linearBindings (protocolResources context))
       && Map.lookup next (linearBindings (protocolResources context)) ==
          Just (TyEndpoint expectedHead))
    (label <> ": wrong exact linear resource projection")
  case Map.lookup next (protocolEndpoints context) of
    Just binding ->
      expect (protocolEndpointName binding == next
           && protocolEndpointInstance binding == revision
           && protocolEndpointRole binding == role
           && protocolEndpointSession binding == expectedHead)
        (label <> ": wrong exact nominal or session successor")
    Nothing -> Left (label <> ": missing exact successor endpoint")
