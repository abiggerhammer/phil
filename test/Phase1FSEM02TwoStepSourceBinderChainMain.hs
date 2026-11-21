{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 NON-NORMATIVE: a *bounded* whole-source two-action binder chain.
-- This independently checks concrete Grammar-v1 syntax and actual production
-- binder identity, protocol projection and Core.Protocol transitions. It is
-- NOT the general component elaborator or universal source/target refinement.
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
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..), GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..), grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

data ChainError
  = ChainUnsupportedSourceShape
  | ChainUnresolvedOccurrence
  | ChainFirstEndpointNotParameter
  | ChainSecondPredecessorMismatch
  | ChainTerminalCloseMismatch
  | ChainPatternShape
  | ChainBinderError String
  deriving (Eq, Show)

data CheckedChain = CheckedChain
  { chainBefore :: Name
  , chainMiddle :: Name
  , chainFinal :: Name
  } deriving (Eq, Show)

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
  let cases =
        [ ("two source-checked binder generations replay exact native two-step endpoints",
            sourceReplay accepted)
        , ("source second-step stale predecessor rejects at the exact chain gate",
            expectClientError ChainSecondPredecessorMismatch staleSource)
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

-- Production lexical identity is the authority for distinguishing source
-- occurrences. Name spelling is *never* used as a Core endpoint identity.
local :: GrammarV1LexicalScope -> Located GrammarV1Expression
      -> Either ChainError GrammarV1ResolvedBinder
local scope source =
  maybe (Left ChainUnresolvedOccurrence)
    (Right . grammarV1CheckedLocalValueBinder)
    (grammarV1CheckedLocalValueOccurrenceInScope scope source)

bindOne :: Located GrammarV1Pattern -> GrammarV1LexicalScope
        -> Either ChainError (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindOne patternSource scope = do
  (binders, after) <- mapLeft (ChainBinderError . show) $
    grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope
  case binders of
    [one] -> Right (one, after)
    _ -> Left ChainPatternShape

bindReceive :: Located GrammarV1Pattern -> GrammarV1LexicalScope
            -> Either ChainError (GrammarV1ResolvedBinder, GrammarV1LexicalScope)
bindReceive patternSource scope =
  case locatedValue patternSource of
    GrammarV1TuplePattern [_, _] -> do
      (binders, after) <- mapLeft (ChainBinderError . show) $
        grammarV1BindPattern GrammarV1LetPatternBinder patternSource scope
      case binders of
        [endpoint, _payload] -> Right (endpoint, after)
        _ -> Left ChainPatternShape
    _ -> Left ChainPatternShape

checkSendChain :: DeclarationKey -> GrammarV1ComponentDecl
               -> Either ChainError CheckedChain
checkSendChain declaration component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement p1 e1)
      , Located _ (GrammarV1LetStatement p2 e2)
      , Located _ (GrammarV1ExpressionStatement eClose)
      ] -> case (locatedValue e1, locatedValue e2, locatedValue eClose) of
        ( GrammarV1SendExpression payload1 endpoint1
          , GrammarV1SendExpression payload2 endpoint2
          , GrammarV1CloseExpression closed
          ) -> do
            (_, scope0) <- mapLeft (ChainBinderError . show) $
              grammarV1ComponentParameterScope declaration component
            p1Binder <- local scope0 payload1
            p2Binder <- local scope0 payload2
            first <- local scope0 endpoint1
            expectChain (grammarV1ResolvedBinderKind first ==
              GrammarV1ComponentParameterBinder &&
              grammarV1ResolvedBinderKind p1Binder ==
              GrammarV1ComponentParameterBinder &&
              grammarV1ResolvedBinderKind p2Binder ==
              GrammarV1ComponentParameterBinder)
              ChainFirstEndpointNotParameter
            (middle, scope1) <- bindOne p1 scope0
            usedMiddle <- local scope1 endpoint2
            expectChain (sameBinder usedMiddle middle) ChainSecondPredecessorMismatch
            (final, scope2) <- bindOne p2 scope1
            closedBinder <- local scope2 closed
            expectChain (sameBinder final closedBinder) ChainTerminalCloseMismatch
            pure $ CheckedChain (core first) (core middle) (core final)
        _ -> Left ChainUnsupportedSourceShape
    _ -> Left ChainUnsupportedSourceShape

checkReceiveChain :: DeclarationKey -> GrammarV1ComponentDecl
                  -> Either ChainError CheckedChain
checkReceiveChain declaration component =
  case locatedValue (grammarV1ComponentBody component) of
    GrammarV1Block
      [ Located _ (GrammarV1LetStatement p1 e1)
      , Located _ (GrammarV1LetStatement p2 e2)
      , Located _ (GrammarV1ExpressionStatement eClose)
      ] -> case (locatedValue e1, locatedValue e2, locatedValue eClose) of
        ( GrammarV1ReceiveExpression _type1 endpoint1
          , GrammarV1ReceiveExpression _type2 endpoint2
          , GrammarV1CloseExpression closed
          ) -> do
            (_, scope0) <- mapLeft (ChainBinderError . show) $
              grammarV1ComponentParameterScope declaration component
            first <- local scope0 endpoint1
            expectChain (grammarV1ResolvedBinderKind first ==
              GrammarV1ComponentParameterBinder)
              ChainFirstEndpointNotParameter
            (middle, scope1) <- bindReceive p1 scope0
            usedMiddle <- local scope1 endpoint2
            expectChain (sameBinder usedMiddle middle) ChainSecondPredecessorMismatch
            (final, scope2) <- bindReceive p2 scope1
            closedBinder <- local scope2 closed
            expectChain (sameBinder final closedBinder) ChainTerminalCloseMismatch
            pure $ CheckedChain (core first) (core middle) (core final)
        _ -> Left ChainUnsupportedSourceShape
    _ -> Left ChainUnsupportedSourceShape

expectChain :: Bool -> ChainError -> Either ChainError ()
expectChain True _ = Right ()
expectChain False err = Left err

sameBinder :: GrammarV1ResolvedBinder -> GrammarV1ResolvedBinder -> Bool
sameBinder one other =
  grammarV1ResolvedBinderKey one == grammarV1ResolvedBinderKey other

core :: GrammarV1ResolvedBinder -> Name
core = grammarV1ResolvedBinderCoreName

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
