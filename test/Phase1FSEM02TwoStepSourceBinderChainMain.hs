{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE: complete-source test of the *production library's*
-- bounded two-step component checker, projected heads, and native Core replay.
-- This does NOT prove general compiler elaboration or Haskell/Rocq refinement.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.ComponentTwoStepChain
  ( ChainError (..), CheckedChain (..), checkSendChain, checkReceiveChain )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

data SourcePair = SourcePair
  { pairRevision :: ProtocolInstanceRevision
  , pairClientHead :: Session
  , pairServerHead :: Session
  , pairClient :: CheckedChain
  , pairServer :: CheckedChain
  }

main :: IO ()
main = do
  accepted <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil"
  staleSource <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/second-stale.phil"
  badClose <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/wrong-close.phil"
  localPayload <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/second-local-payload.phil"
  wrongFirstReceiveType <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/receive-first-u16.phil"
  wrongSecondReceiveType <- TextIO.readFile "test/fixtures/fsem02-two-step-source-chain-v1/receive-second-u16.phil"
  let cases =
        [ ("two source-checked binder generations replay exact native two-step endpoints",
            sourceReplay accepted)
        , ("source second-step stale predecessor rejects at the exact chain gate",
            expectClientError ChainSecondPredecessorMismatch staleSource)
        , ("post-first-let endpoint payload is bound, but not a source parameter",
            expectClientError ChainSecondPayloadNotParameter localPayload)
        , ("first Receive annotation outside DoublePing U8 envelope rejects exactly",
            expectServerError ChainFirstReceiveAnnotationNotU8 wrongFirstReceiveType)
        , ("second Receive annotation outside DoublePing U8 envelope rejects exactly",
            expectServerError ChainSecondReceiveAnnotationNotU8 wrongSecondReceiveType)
        , ("source terminal close of first successor rejects at exact chain gate",
            expectClientError ChainTerminalCloseMismatch badClose)
        ]
  results <- mapM (\(label, outcome) -> case outcome of
    Right () -> putStrLn ("PASS: " <> label) >> pure True
    Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False) cases
  if and results then pure () else exitFailure

expect :: Bool -> String -> Either String ()
expect True _ = Right ()
expect False err = Left err

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

sourcePair :: Text.Text -> Either String SourcePair
sourcePair source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-two-step-source" source)
  let decls = map (locatedValue . grammarV1Declaration . locatedValue)
        (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- decls]
      components = [c | GrammarV1ComponentDeclaration c <- decls]
      programs = [p | GrammarV1ProgramDeclaration p <- decls]
  (protocol, client, server) <- case (protocols, components, programs) of
    ([p], [c, s], [_]) -> Right (p, c, s)
    _ -> Left "expected one complete protocol, two components, one selected program"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.DoublePing")
      (InterfaceRevision "protocol.DoublePing.v1") protocol of
    Just (Right value) -> Right value
    other -> Left ("source protocol not accepted as a closed dual family: " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  let clientRole = ProtocolRoleKey "Client"
      serverRole = ProtocolRoleKey "Server"
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  checkedClient <- mapLeft show $
    checkSendChain (DeclarationKey "component.ClientWorker") client
  checkedServer <- mapLeft show $
    checkReceiveChain (DeclarationKey "component.ServerWorker") server
  let expectedClient = Send (Name "x") (TyUInt 8)
        (Send (Name "y") (TyUInt 8) (End (Outcome "Done")))
      expectedServer = Receive (Name "x") (TyUInt 8)
        (Receive (Name "y") (TyUInt 8) (End (Outcome "Done")))
  expect (protocolProjectionSession clientProjection == expectedClient
       && protocolProjectionSession serverProjection == expectedServer)
    "source family did not produce exact dual two-message U8 projections"
  pure SourcePair
    { pairRevision = binaryProtocolInstanceRevision instanceValue
    , pairClientHead = protocolProjectionSession clientProjection
    , pairServerHead = protocolProjectionSession serverProjection
    , pairClient = checkedClient
    , pairServer = checkedServer
    }

expectClientError :: ChainError -> Text.Text -> Either String ()
expectClientError expected source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-negative-source" source)
  let decls = map (locatedValue . grammarV1Declaration . locatedValue)
        (grammarV1TopLevelDecls parsed)
      clients = [c | GrammarV1ComponentDeclaration c <- decls]
  case clients of
    client : _ ->
      case checkSendChain (DeclarationKey "component.ClientWorker") client of
        Left actual | actual == expected -> Right ()
        other -> Left ("expected exact source error " <> show expected
          <> ", got " <> show other)
    _ -> Left "negative source was not structurally parsed as a component"

expectServerError :: ChainError -> Text.Text -> Either String ()
expectServerError expected source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-negative-receive-source" source)
  let decls = map (locatedValue . grammarV1Declaration . locatedValue)
        (grammarV1TopLevelDecls parsed)
      components = [c | GrammarV1ComponentDeclaration c <- decls]
  case components of
    [_client, server] ->
      case checkReceiveChain (DeclarationKey "component.ServerWorker") server of
        Left actual | actual == expected -> Right ()
        other -> Left ("expected exact source receive error " <> show expected
          <> ", got " <> show other)
    _ -> Left "negative source must contain exactly two parsed components"

sourceReplay :: Text.Text -> Either String ()
sourceReplay source = do
  pair <- sourcePair source
  let revision = pairRevision pair
      client = ProtocolRoleKey "Client"
      server = ProtocolRoleKey "Server"
      c = pairClient pair
      s = pairServer pair
      send old next = ProtocolSendRequest old next revision client
      receive old next = ProtocolReceiveRequest old next revision server
  expect (allDistinct (map chainBefore [c, s] ++
                       map chainMiddle [c, s] ++
                       map chainFinal [c, s]))
    "source binder ordinals collided across component declaration roots"
  c0 <- mapLeft show $
    insertProtocolEndpoint (chainBefore c) revision client
      (pairClientHead pair) emptyProtocolContext
  s0 <- mapLeft show $
    insertProtocolEndpoint (chainBefore s) revision server
      (pairServerHead pair) emptyProtocolContext
  c1 <- mapLeft show $ checkProtocolAction
    (send (chainBefore c) (chainMiddle c)) c0
  s1 <- mapLeft show $ checkProtocolAction
    (receive (chainBefore s) (chainMiddle s)) s0
  let cm = checkedProtocolContext c1
      sm = checkedProtocolContext s1
  checkStep "client first" cm (chainBefore c) (chainMiddle c)
    (Send (Name "y") (TyUInt 8) (End (Outcome "Done")))
  checkStep "server first" sm (chainBefore s) (chainMiddle s)
    (Receive (Name "y") (TyUInt 8) (End (Outcome "Done")))
  -- The second action cannot consume the initial predecessor again.
  stale "client" (send (chainBefore c) (chainFinal c)) (chainBefore c) cm
  stale "server" (receive (chainBefore s) (chainFinal s)) (chainBefore s) sm
  c2 <- mapLeft show $ checkProtocolAction
    (send (chainMiddle c) (chainFinal c)) cm
  s2 <- mapLeft show $ checkProtocolAction
    (receive (chainMiddle s) (chainFinal s)) sm
  let cf = checkedProtocolContext c2
      sf = checkedProtocolContext s2
  checkStep "client second" cf (chainMiddle c) (chainFinal c) (End (Outcome "Done"))
  checkStep "server second" sf (chainMiddle s) (chainFinal s) (End (Outcome "Done"))
  expect (Map.notMember (chainBefore c) (protocolEndpoints cf)
       && Map.notMember (chainBefore s) (protocolEndpoints sf))
    "second step resurrected first-generation endpoint"
  cc <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest (chainFinal c) revision client (Outcome "Done")) cf
  sc <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest (chainFinal s) revision server (Outcome "Done")) sf
  expect (Map.null (protocolEndpoints (checkedProtocolContext cc))
       && Map.null (protocolEndpoints (checkedProtocolContext sc)))
    "one or both terminal endpoints remain after Close"

allDistinct :: Ord a => [a] -> Bool
allDistinct values = Set.size (Set.fromList values) == length values

stale :: String -> ProtocolActionRequest -> Name -> ProtocolContext
      -> Either String ()
stale label request old context =
  case checkProtocolAction request context of
    Left (ProtocolEndpointUnknown name) | name == old -> Right ()
    other -> Left (label <> ": expected exact stale predecessor, got " <> show other)

checkStep :: String -> ProtocolContext -> Name -> Name -> Session
          -> Either String ()
checkStep label context old next headSession = do
  let endpoints = protocolEndpoints context
      resources = protocolResources context
  expect (Map.size endpoints == 1 && Map.notMember old endpoints)
    (label <> ": predecessor still live or endpoint count changed")
  case Map.lookup next endpoints of
    Just endpoint ->
      expect (protocolEndpointSession endpoint == headSession)
        (label <> ": wrong source-derived continuation session")
    Nothing -> Left (label <> ": missing exact source-derived successor")
  expect (Map.size (linearBindings resources) == 1 &&
          Map.lookup next (linearBindings resources) == Just (TyEndpoint headSession) &&
          Map.notMember old (linearBindings resources))
    (label <> ": exact native linear resource map disagrees with source binder chain")
