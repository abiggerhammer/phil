{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 finite source-to-production choice progression / failure bridge.
-- Not a universal source typing or Haskell-to-Rocq simulation theorem.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionAction (..), SessionError (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Branch (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentSelectClose
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  accepted <- TextIO.readFile "test/fixtures/fsem02-source-choice-v1/accepted.phil"
  unknown <- TextIO.readFile "test/fixtures/fsem02-source-choice-v1/unknown-label.phil"
  stale <- TextIO.readFile "test/fixtures/fsem02-source-choice-v1/stale-close.phil"
  passed <- sequence
    [ test "FSEM-02 source-selected Go and Core offered Go retire predecessors, preserve exact successor" $
        acceptedSourceSelectAndCoreOffer accepted
    , test "FSEM-02 one-token unknown source choice rejects with exact Core label class" $
        unknownSourceLabelRejected unknown
    , test "FSEM-02 one-operand stale close fails at the source binder authority" $
        staleSourceCloseRejected stale
    , test "FSEM-02 wrong head and protocol identity do not advance source predecessor" $
        wrongHeadAndInstanceRejected accepted
    ]
  if and passed then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

data SourceChoice = SourceChoice
  { choiceClient :: GrammarV1CheckedComponentSelectClose
  , choiceInstance :: ProtocolInstanceRevision
  , choiceClientHead :: Session
  , choiceServerHead :: Session
  }

sourceChoice :: Text.Text -> Either String SourceChoice
sourceChoice source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-source-choice-v1" source)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  (protocol, component) <- case (protocols, components, programs) of
    ([p], [c], [_]) -> Right (p, c)
    _ -> Left "source witness must contain one protocol, client, and root program"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.Choice")
      (InterfaceRevision "protocol.Choice.v1")
      protocol of
    Just (Right x) -> Right x
    other -> Left ("choice source protocol failed closed dual-role validation: " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  clientProjection <- mapLeft show $ projectProtocolRole instanceValue clientRole
  serverProjection <- mapLeft show $ projectProtocolRole instanceValue serverRole
  client <- case grammarV1CheckedComponentSelectClose
      (DeclarationKey "component.ClientWorker") component of
    Just (Right x) -> Right x
    other -> Left ("source select/close was not checked: " <> show other)
  let clientSession = protocolProjectionSession clientProjection
      serverSession = protocolProjectionSession serverProjection
  assert (clientSession == Select choiceBranches
       && serverSession == Offer choiceBranches)
    "source role projection did not preserve exact dual Go/Cancel heads"
  Right SourceChoice
    { choiceClient = client
    , choiceInstance = binaryProtocolInstanceRevision instanceValue
    , choiceClientHead = clientSession
    , choiceServerHead = serverSession
    }

choiceBranches :: [Branch]
choiceBranches =
  [ Branch { branchLabel = "Go", branchPayload = Nothing,
             branchContinuation = End (Outcome "Done") }
  , Branch { branchLabel = "Cancel", branchPayload = Nothing,
             branchContinuation = End (Outcome "Cancel") }
  ]

acceptedSourceSelectAndCoreOffer :: Text.Text -> Either String ()
acceptedSourceSelectAndCoreOffer source = do
  plan <- sourceChoice source
  let checked = choiceClient plan
      old = grammarV1ResolvedBinderCoreName (checkedComponentSelectEndpoint checked)
      next = grammarV1ResolvedBinderCoreName (checkedComponentSelectSuccessor checked)
      instanceRevision = choiceInstance plan
      serverOld = Name "core.external.server.old"
      serverNext = Name "core.external.server.next"
  assert (old /= next && checkedComponentSelectLabel checked == "Go")
    "source label or fresh binder identity changed"
  clientContext <- mapLeft show $
    insertProtocolEndpoint old instanceRevision clientRole
      (choiceClientHead plan) emptyProtocolContext
  serverContext <- mapLeft show $
    insertProtocolEndpoint serverOld instanceRevision serverRole
      (choiceServerHead plan) emptyProtocolContext
  clientAdvanced <- mapLeft show $ checkProtocolAction
    (ProtocolSelectRequest old next instanceRevision clientRole
      (checkedComponentSelectLabel checked)) clientContext
  serverAdvanced <- mapLeft show $ checkProtocolAction
    (ProtocolOfferRequest serverOld serverNext instanceRevision serverRole
      "Go") serverContext
  exactSuccessor old next instanceRevision clientRole clientAdvanced
  exactSuccessor serverOld serverNext instanceRevision serverRole serverAdvanced
  case checkProtocolAction
      (ProtocolSelectRequest old (Name "stale") instanceRevision clientRole "Go")
      (checkedProtocolContext clientAdvanced) of
    Left (ProtocolEndpointUnknown observed) ->
      assert (observed == old) "replayed source-selected predecessor identity changed"
    other -> Left ("consumed select predecessor was reused: " <> show other)
  case checkProtocolAction
      (ProtocolOfferRequest serverOld (Name "stale") instanceRevision serverRole "Go")
      (checkedProtocolContext serverAdvanced) of
    Left (ProtocolEndpointUnknown observed) ->
      assert (observed == serverOld) "external offer predecessor identity changed"
    other -> Left ("consumed offer predecessor was reused: " <> show other)
  clientClosed <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest next instanceRevision clientRole (Outcome "Done"))
    (checkedProtocolContext clientAdvanced)
  serverClosed <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest serverNext instanceRevision serverRole (Outcome "Done"))
    (checkedProtocolContext serverAdvanced)
  assert (checkedProtocolSuccessor clientClosed == Nothing
       && checkedProtocolSuccessor serverClosed == Nothing)
    "terminal close unexpectedly created an endpoint"
  assert (Map.null (protocolEndpoints (checkedProtocolContext clientClosed))
       && Map.null (protocolEndpoints (checkedProtocolContext serverClosed))
       && Map.null (linearBindings (protocolResources (checkedProtocolContext clientClosed)))
       && Map.null (linearBindings (protocolResources (checkedProtocolContext serverClosed))))
    "terminal close retained the source-selected or Core-only offered owner"

exactSuccessor
  :: Name -> Name -> ProtocolInstanceRevision -> ProtocolRoleKey
  -> CheckedProtocolStep -> Either String ()
exactSuccessor old next instanceRevision role checked = do
  binding <- maybe (Left "continuation not allocated") Right (checkedProtocolSuccessor checked)
  assert (protocolEndpointName binding == next
       && protocolEndpointSession binding == End (Outcome "Done")
       && protocolEndpointInstance binding == instanceRevision
       && protocolEndpointRole binding == role)
    "continuation changed endpoint name/session/instance/role"
  let context = checkedProtocolContext checked
  assert (Map.notMember old (protocolEndpoints context)
       && Map.notMember old (linearBindings (protocolResources context))
       && Map.lookup next (linearBindings (protocolResources context))
          == Just (TyEndpoint (End (Outcome "Done"))))
    "Core predecessor retirement or continuation typing changed"

unknownSourceLabelRejected :: Text.Text -> Either String ()
unknownSourceLabelRejected source = do
  plan <- sourceChoice source
  let checked = choiceClient plan
      old = grammarV1ResolvedBinderCoreName (checkedComponentSelectEndpoint checked)
      next = grammarV1ResolvedBinderCoreName (checkedComponentSelectSuccessor checked)
      instanceRevision = choiceInstance plan
  assert (checkedComponentSelectLabel checked == "Absent")
    "unknown-label fixture was not derived from the parsed source label"
  initial <- mapLeft show $
    insertProtocolEndpoint old instanceRevision clientRole
      (choiceClientHead plan) emptyProtocolContext
  case checkProtocolAction
      (ProtocolSelectRequest old next instanceRevision clientRole
        (checkedComponentSelectLabel checked)) initial of
    Left (ProtocolSessionError (UnknownSessionLabel actual available)) ->
      assert (actual == "Absent" && available == ["Go","Cancel"])
        "label rejection lost exact requested/available source choices"
    other -> Left ("unsupported source label escaped Core type checking: " <> show other)

staleSourceCloseRejected :: Text.Text -> Either String ()
staleSourceCloseRejected source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-stale-choice" source)
  let components =
        [ c
        | Located _ top <- grammarV1TopLevelDecls parsed
        , GrammarV1ComponentDeclaration c <- [locatedValue (grammarV1Declaration top)]
        ]
  case components of
    [client] -> case grammarV1CheckedComponentSelectClose
        (DeclarationKey "component.ClientWorker") client of
      Just (Left (GrammarV1ComponentSelectCloseCloseMismatch expected actual)) ->
        assert (grammarV1ResolvedBinderDisplayName expected == "chosen"
             && grammarV1ResolvedBinderDisplayName actual == "endpoint")
          "stale close did not identify chosen successor versus retired endpoint"
      other -> Left ("stale close was not precisely rejected: " <> show other)
    _ -> Left "stale fixture lost the client component"

wrongHeadAndInstanceRejected :: Text.Text -> Either String ()
wrongHeadAndInstanceRejected source = do
  plan <- sourceChoice source
  let checked = choiceClient plan
      old = grammarV1ResolvedBinderCoreName (checkedComponentSelectEndpoint checked)
      next = grammarV1ResolvedBinderCoreName (checkedComponentSelectSuccessor checked)
      instanceRevision = choiceInstance plan
  initial <- mapLeft show $
    insertProtocolEndpoint old instanceRevision clientRole
      (choiceClientHead plan) emptyProtocolContext
  case checkProtocolAction
      (ProtocolOfferRequest old next instanceRevision clientRole "Go") initial of
    Left (ProtocolSessionError (UnexpectedSessionAction (OfferAction label) actual)) ->
      assert (label == "Go" && actual == choiceClientHead plan)
        "wrong-session-head diagnostic drift"
    other -> Left ("source select unexpectedly admitted offer: " <> show other)
  case checkProtocolAction
      (ProtocolSelectRequest old next
        (ProtocolInstanceRevision "wrong-explicit-instance") clientRole "Go") initial of
    Left (ProtocolInstanceMismatch observed requested actual) ->
      assert (observed == old
           && requested == ProtocolInstanceRevision "wrong-explicit-instance"
           && actual == instanceRevision)
        "wrong-instance rejection lost exact protocol authority"
    other -> Left ("wrong instance was silently admitted: " <> show other)

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

assert :: Bool -> String -> Either String ()
assert ok why = if ok then Right () else Left why

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
