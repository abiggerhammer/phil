{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE: exact collision refusals at both native
-- two-generation Send/Receive boundaries. Explicit protocol and frame inputs
-- do not derive any authority from accepted source syntax.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context
  ( CheckError (DuplicateBinding), ResourceContext (..), insertBinding, startSharedLoan )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionError (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Mode (Affine, Unrestricted), Name (..), Outcome (..), Session (..), Ty (..))
import System.Exit (exitFailure)

main :: IO ()
main = case successorCollisionFrame of
  Right () -> putStrLn "PASS: native two-step successor occupancy, refusal, and retry frame"
  Left err -> putStrLn ("FAIL: " <> err) >> exitFailure

expect :: Bool -> String -> Either String ()
expect True _ = Right ()
expect False message = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

spectatorRevision :: ProtocolInstanceRevision
spectatorRevision = ProtocolInstanceRevision "fsem02.unrelated.protocol.v1"

spectatorRole :: ProtocolRoleKey
spectatorRole = ProtocolRoleKey "Observer"

spectatorSession :: Session
spectatorSession = End (Outcome "OtherDone")

withFrame :: Name -> Name -> Name -> ProtocolContext -> Either String ProtocolContext
withFrame spectator loan plain context = do
  withSpectator <- mapLeft show $
    insertProtocolEndpoint spectator spectatorRevision spectatorRole spectatorSession context
  withAffine <- mapLeft show $
    insertBinding Affine loan (TyUInt 8) (protocolResources withSpectator)
  withLoan <- mapLeft show $ startSharedLoan loan withAffine
  withPlain <- mapLeft show $ insertBinding Unrestricted plain TyBool withLoan
  pure (withSpectator {protocolResources = withPlain})

-- Any occupied successor must be rejected with the *specific* native error.
-- No CheckedProtocolStep means no successor resource or metadata escapes.
occupiedRefusal :: String -> ProtocolActionRequest -> Name -> ProtocolContext -> Either String ()
occupiedRefusal label request successor context =
  case checkProtocolAction request context of
    Left (ProtocolSessionError (SessionResourceError (DuplicateBinding name)))
      | name == successor -> Right ()
    other -> Left (label <> ": expected exact DuplicateBinding " <> show successor
      <> ", got " <> show other)

sameNameRefusal :: String -> ProtocolActionRequest -> Name -> ProtocolContext -> Either String ()
sameNameRefusal label request predecessor context =
  case checkProtocolAction request context of
    Left (ProtocolSessionError (SuccessorReusesEndpointName name))
      | name == predecessor -> Right ()
    other -> Left (label <> ": expected exact SuccessorReusesEndpointName "
      <> show predecessor <> ", got " <> show other)

-- Exact native metadata plus all four disjoint structural resources at
-- initial, committed, post-refusal retry, and terminal checkpoints.
checkpoint
  :: String -> ProtocolContext -> ProtocolInstanceRevision -> ProtocolRoleKey
  -> Maybe (Name, Session) -> [Name] -> Name -> Name -> Name
  -> Either String ()
checkpoint label context revision role active consumed spectator loan plain = do
  let resources = protocolResources context
      endpoints = protocolEndpoints context
      liveCount = maybe 1 (const 2) active
  expect (Map.size endpoints == liveCount &&
          Map.size (linearBindings resources) == liveCount)
    (label <> ": endpoint/linear count mismatch")
  expect (Map.lookup spectator endpoints ==
            Just (ProtocolEndpointBinding spectator spectatorRevision spectatorRole spectatorSession) &&
          Map.lookup spectator (linearBindings resources) == Just (TyEndpoint spectatorSession))
    (label <> ": spectator identity or resource overwritten")
  expect (Map.size (affineBindings resources) == 1 &&
          Map.lookup loan (affineBindings resources) == Just (TyUInt 8) &&
          sharedLoans resources == Set.singleton loan)
    (label <> ": active borrowed affine owner changed")
  expect (Map.size (unrestrictedBindings resources) == 1 &&
          Map.lookup plain (unrestrictedBindings resources) == Just TyBool)
    (label <> ": unrelated unrestricted owner changed")
  expect (all (\name -> Map.notMember name endpoints &&
                        Map.notMember name (linearBindings resources)) consumed)
    (label <> ": consumed predecessor still live")
  case active of
    Nothing -> Right ()
    Just (name, headSession) -> do
      expect (Map.lookup name endpoints ==
                Just (ProtocolEndpointBinding name revision role headSession))
        (label <> ": active endpoint nominal identity/head mismatch")
      expect (Map.lookup name (linearBindings resources) ==
                Just (TyEndpoint headSession))
        (label <> ": active endpoint resource/head mismatch")

successorCollisionFrame :: Either String ()
successorCollisionFrame = do
  let client = ProtocolRoleKey "Client"
      server = ProtocolRoleKey "Server"
      first = Name "first"
      second = Name "second"
      done = Outcome "Done"
      client0 = Name "client0"
      client1 = Name "client1"
      client2 = Name "client2"
      server0 = Name "server0"
      server1 = Name "server1"
      server2 = Name "server2"
      cSpectator = Name "c-spectator"
      sSpectator = Name "s-spectator"
      cLoan = Name "c-borrowed"
      sLoan = Name "s-borrowed"
      cPlain = Name "c-unrestricted"
      sPlain = Name "s-unrestricted"
      cMiddle = Send second (TyUInt 8) (End done)
      sMiddle = Receive second (TyUInt 8) (End done)
      cInitial = Send first (TyUInt 8) cMiddle
      sInitial = Receive first (TyUInt 8) sMiddle
      family = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = DeclarationKey "protocol.FSEM02OccupiedSuccessor"
        , protocolFamilyInterfaceRevision = InterfaceRevision "protocol.FSEM02OccupiedSuccessor.v1"
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
  cProjection <- mapLeft show $ projectProtocolRole instanceValue client
  sProjection <- mapLeft show $ projectProtocolRole instanceValue server
  expect (protocolProjectionSession cProjection == cInitial &&
          protocolProjectionSession sProjection == sInitial)
    "externally instantiated protocol did not project exact dual heads"
  let revision = binaryProtocolInstanceRevision instanceValue
      send predecessor successor = ProtocolSendRequest predecessor successor revision client
      receive predecessor successor = ProtocolReceiveRequest predecessor successor revision server
      check label ctx role active gone spectator loan plain =
        checkpoint label ctx revision role active gone spectator loan plain

  cInitialContext <- mapLeft show $
    insertProtocolEndpoint client0 revision client cInitial emptyProtocolContext
  sInitialContext <- mapLeft show $
    insertProtocolEndpoint server0 revision server sInitial emptyProtocolContext
  cBefore <- withFrame cSpectator cLoan cPlain cInitialContext
  sBefore <- withFrame sSpectator sLoan sPlain sInitialContext
  check "client initial" cBefore client (Just (client0, cInitial)) [] cSpectator cLoan cPlain
  check "server initial" sBefore server (Just (server0, sInitial)) [] sSpectator sLoan sPlain

  -- First-generation attempted collisions must not consume the originals.
  occupiedRefusal "client first spectator" (send client0 cSpectator) cSpectator cBefore
  occupiedRefusal "server first loan" (receive server0 sLoan) sLoan sBefore
  check "client still initial" cBefore client (Just (client0, cInitial)) [] cSpectator cLoan cPlain
  check "server still initial" sBefore server (Just (server0, sInitial)) [] sSpectator sLoan sPlain
  cFirst <- mapLeft show $ checkProtocolAction (send client0 client1) cBefore
  sFirst <- mapLeft show $ checkProtocolAction (receive server0 server1) sBefore
  let cCommitted = checkedProtocolContext cFirst
      sCommitted = checkedProtocolContext sFirst
  check "client first committed" cCommitted client (Just (client1, cMiddle)) [client0] cSpectator cLoan cPlain
  check "server first committed" sCommitted server (Just (server1, sMiddle)) [server0] sSpectator sLoan sPlain

  -- The second step must refuse each of the three occupied structural maps
  -- and the predecessor name on both peers; the committed prefix remains.
  occupiedRefusal "client second spectator" (send client1 cSpectator) cSpectator cCommitted
  occupiedRefusal "client second loan" (send client1 cLoan) cLoan cCommitted
  occupiedRefusal "client second unrestricted" (send client1 cPlain) cPlain cCommitted
  occupiedRefusal "server second spectator" (receive server1 sSpectator) sSpectator sCommitted
  occupiedRefusal "server second loan" (receive server1 sLoan) sLoan sCommitted
  occupiedRefusal "server second unrestricted" (receive server1 sPlain) sPlain sCommitted
  sameNameRefusal "client second same-name" (send client1 client1) client1 cCommitted
  sameNameRefusal "server second same-name" (receive server1 server1) server1 sCommitted
  check "client after refusals" cCommitted client (Just (client1, cMiddle)) [client0] cSpectator cLoan cPlain
  check "server after refusals" sCommitted server (Just (server1, sMiddle)) [server0] sSpectator sLoan sPlain

  -- A distinct fresh continuation succeeds from the *same* committed input.
  cSecond <- mapLeft show $ checkProtocolAction (send client1 client2) cCommitted
  sSecond <- mapLeft show $ checkProtocolAction (receive server1 server2) sCommitted
  let cFinal = checkedProtocolContext cSecond
      sFinal = checkedProtocolContext sSecond
  check "client second committed" cFinal client (Just (client2, End done))
    [client0, client1] cSpectator cLoan cPlain
  check "server second committed" sFinal server (Just (server2, End done))
    [server0, server1] sSpectator sLoan sPlain
  cClose <- mapLeft show $ checkProtocolAction (ProtocolCloseRequest client2 revision client done) cFinal
  sClose <- mapLeft show $ checkProtocolAction (ProtocolCloseRequest server2 revision server done) sFinal
  check "client closed" (checkedProtocolContext cClose) client Nothing
    [client0, client1, client2] cSpectator cLoan cPlain
  check "server closed" (checkedProtocolContext sClose) server Nothing
    [server0, server1, server2] sSpectator sLoan sPlain
