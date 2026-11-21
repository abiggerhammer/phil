{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE: finite two-step native Core.Protocol frame check.
-- External protocol instance and independent spectator/loan inputs are explicit.
-- Complete-source admitted single-step fixtures run separately in strict CI.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context
  ( ResourceContext (..), endSharedLoan, insertBinding, startSharedLoan )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionAction (..), SessionError (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Mode (Affine), Name (..), Outcome (..), Session (..), Ty (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  result <- runCase "two-step native endpoints preserve disjoint spectator and active affine loan" spectatorLoanFrame
  if result then pure () else exitFailure

runCase :: String -> Either String () -> IO Bool
runCase label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

expect :: Bool -> String -> Either String ()
expect True _ = Right ()
expect False err = Left err

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

spectatorRevision :: ProtocolInstanceRevision
spectatorRevision = ProtocolInstanceRevision "fsem02.disjoint.spectator.v1"

spectatorRole :: ProtocolRoleKey
spectatorRole = ProtocolRoleKey "IndependentObserver"

spectatorSession :: Session
spectatorSession = End (Outcome "SpectatorDone")

-- This test input does not grant source-selected protocol/architecture authority.
withIndependentFrame :: Name -> Name -> ProtocolContext -> Either String ProtocolContext
withIndependentFrame spectator loanOwner ctx = do
  withSpectator <- mapLeft show $
    insertProtocolEndpoint spectator spectatorRevision spectatorRole spectatorSession ctx
  withAffine <- mapLeft show $
    insertBinding Affine loanOwner (TyUInt 8) (protocolResources withSpectator)
  borrowed <- mapLeft show $ startSharedLoan loanOwner withAffine
  pure (withSpectator {protocolResources = borrowed})

-- Inspect ALL four resource collections, exact protocol metadata, and exact
-- predecessor absence. The spectator endpoint is not a source-derived actor.
checkCheckpoint
  :: String -> ProtocolContext -> [Name] -> Maybe (Name, Session)
  -> ProtocolInstanceRevision -> ProtocolRoleKey -> Name -> Name
  -> Either String ()
checkCheckpoint label ctx absent current revision role spectator loanOwner = do
  let resources = protocolResources ctx
      endpoints = protocolEndpoints ctx
      liveCount = maybe 1 (const 2) current
      spectatorBinding =
        ProtocolEndpointBinding spectator spectatorRevision spectatorRole spectatorSession
  expect (Map.size endpoints == liveCount &&
          Map.size (linearBindings resources) == liveCount)
    (label <> ": incorrect exact endpoint/linear cardinality")
  expect (Map.lookup spectator endpoints == Just spectatorBinding &&
          Map.lookup spectator (linearBindings resources) ==
            Just (TyEndpoint spectatorSession))
    (label <> ": disjoint spectator identity/resource changed")
  expect (Map.size (affineBindings resources) == 1 &&
          Map.lookup loanOwner (affineBindings resources) == Just (TyUInt 8) &&
          sharedLoans resources == Set.singleton loanOwner &&
          Map.null (unrestrictedBindings resources))
    (label <> ": affine owner, active loan, or unrestricted frame changed")
  expect (all (\name -> Map.notMember name endpoints &&
                        Map.notMember name (linearBindings resources)) absent)
    (label <> ": consumed predecessor unexpectedly remains live")
  case current of
    Nothing -> Right ()
    Just (name, headSession) -> do
      expect (Map.lookup name (linearBindings resources) ==
              Just (TyEndpoint headSession))
        (label <> ": wrong successor linear resource or type")
      expect (Map.lookup name endpoints ==
              Just (ProtocolEndpointBinding name revision role headSession))
        (label <> ": wrong successor nominal instance/role/session")

spectatorLoanFrame :: Either String ()
spectatorLoanFrame = do
  let client = ProtocolRoleKey "Client"
      server = ProtocolRoleKey "Server"
      first = Name "first"
      second = Name "second"
      done = Outcome "Done"
      client0 = Name "client-original"
      client1 = Name "client-middle"
      client2 = Name "client-terminal"
      server0 = Name "server-original"
      server1 = Name "server-middle"
      server2 = Name "server-terminal"
      clientSpectator = Name "client-uninvolved"
      serverSpectator = Name "server-uninvolved"
      clientLoan = Name "client-affine-borrow"
      serverLoan = Name "server-affine-borrow"
      clientMiddle = Send second (TyUInt 8) (End done)
      serverMiddle = Receive second (TyUInt 8) (End done)
      clientInitial = Send first (TyUInt 8) clientMiddle
      serverInitial = Receive first (TyUInt 8) serverMiddle
      family = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = DeclarationKey "protocol.FSEM02TwoStepSpectator"
        , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.FSEM02TwoStepSpectator.v1"
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = client
        , protocolFamilyPeerRole = server
        , protocolFamilyPrimarySession =
            ProtocolTemplateSend first (ProtocolConcreteType (TyUInt 8))
              (ProtocolTemplateSend second (ProtocolConcreteType (TyUInt 8))
                (ProtocolTemplateEnd done))
        }
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue client
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue server
  let revision = binaryProtocolInstanceRevision instanceValue
      send old next = ProtocolSendRequest old next revision client
      receive old next = ProtocolReceiveRequest old next revision server
      checkpoint label ctx absent current role spectator loan =
        checkCheckpoint label ctx absent current revision role spectator loan
  expect (protocolProjectionSession clientProjection == clientInitial &&
          protocolProjectionSession serverProjection == serverInitial)
    "real instantiated protocol did not project the two exact dual U8 heads"

  cBase <- mapLeft show $
    insertProtocolEndpoint client0 revision client clientInitial emptyProtocolContext
  sBase <- mapLeft show $
    insertProtocolEndpoint server0 revision server serverInitial emptyProtocolContext
  cBefore <- withIndependentFrame clientSpectator clientLoan cBase
  sBefore <- withIndependentFrame serverSpectator serverLoan sBase
  checkpoint "client initial" cBefore [] (Just (client0, clientInitial))
    client clientSpectator clientLoan
  checkpoint "server initial" sBefore [] (Just (server0, serverInitial))
    server serverSpectator serverLoan

  cFirst <- mapLeft show $ checkProtocolAction (send client0 client1) cBefore
  sFirst <- mapLeft show $ checkProtocolAction (receive server0 server1) sBefore
  let cCommitted = checkedProtocolContext cFirst
      sCommitted = checkedProtocolContext sFirst
  checkpoint "client first committed" cCommitted [client0]
    (Just (client1, clientMiddle)) client clientSpectator clientLoan
  checkpoint "server first committed" sCommitted [server0]
    (Just (server1, serverMiddle)) server serverSpectator serverLoan

  -- Rejected probes return no successor context and must not roll back the
  -- first committed contexts. Exact constructors, not arbitrary Left values.
  case checkProtocolAction (send client0 (Name "stale-client")) cCommitted of
    Left (ProtocolEndpointUnknown name) | name == client0 -> Right ()
    other -> Left ("stale original sender was not rejected exactly: " <> show other)
  case checkProtocolAction (receive server0 (Name "stale-server")) sCommitted of
    Left (ProtocolEndpointUnknown name) | name == server0 -> Right ()
    other -> Left ("stale original receiver was not rejected exactly: " <> show other)
  case checkProtocolAction
      (ProtocolReceiveRequest client1 (Name "wrong-head") revision client)
      cCommitted of
    Left (ProtocolSessionError (UnexpectedSessionAction ReceiveAction _)) -> Right ()
    other -> Left ("wrong second-step head was not rejected exactly: " <> show other)
  case checkProtocolAction
      (ProtocolSendRequest client1 (Name "wrong-role") revision server)
      cCommitted of
    Left (ProtocolRoleMismatch name expected actual)
      | name == client1 && expected == server && actual == client -> Right ()
    other -> Left ("wrong externally supplied role was not rejected: " <> show other)
  checkpoint "client after rejected probes" cCommitted [client0]
    (Just (client1, clientMiddle)) client clientSpectator clientLoan
  checkpoint "server after rejected probes" sCommitted [server0]
    (Just (server1, serverMiddle)) server serverSpectator serverLoan

  cSecond <- mapLeft show $ checkProtocolAction (send client1 client2) cCommitted
  sSecond <- mapLeft show $ checkProtocolAction (receive server1 server2) sCommitted
  let cFinal = checkedProtocolContext cSecond
      sFinal = checkedProtocolContext sSecond
  checkpoint "client second committed" cFinal [client0, client1]
    (Just (client2, End done)) client clientSpectator clientLoan
  checkpoint "server second committed" sFinal [server0, server1]
    (Just (server2, End done)) server serverSpectator serverLoan

  cClose <- mapLeft show $
    checkProtocolAction (ProtocolCloseRequest client2 revision client done) cFinal
  sClose <- mapLeft show $
    checkProtocolAction (ProtocolCloseRequest server2 revision server done) sFinal
  let cClosed = checkedProtocolContext cClose
      sClosed = checkedProtocolContext sClose
  checkpoint "client after terminal close" cClosed [client0, client1, client2]
    Nothing client clientSpectator clientLoan
  checkpoint "server after terminal close" sClosed [server0, server1, server2]
    Nothing server serverSpectator serverLoan

  -- Explicit end-of-loan changes ONLY the loan collection. Spectator and
  -- borrowed affine owner remain; no implicit disposal/terminal authority.
  cEnded <- mapLeft show $ endSharedLoan clientLoan (protocolResources cClosed)
  sEnded <- mapLeft show $ endSharedLoan serverLoan (protocolResources sClosed)
  expect (Set.null (sharedLoans cEnded) && Set.null (sharedLoans sEnded) &&
          affineBindings cEnded == affineBindings (protocolResources cClosed) &&
          affineBindings sEnded == affineBindings (protocolResources sClosed) &&
          Map.lookup clientSpectator (linearBindings cEnded) ==
            Map.lookup clientSpectator (linearBindings (protocolResources cClosed)) &&
          Map.lookup serverSpectator (linearBindings sEnded) ==
            Map.lookup serverSpectator (linearBindings (protocolResources sClosed)))
    "explicit loan end changed disjoint spectator or affine owner"
