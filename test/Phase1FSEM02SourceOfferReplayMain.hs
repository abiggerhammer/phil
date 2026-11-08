{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: source-checked unit offer arm + externally selected Core local step.
-- This test does not supply a scheduler, rendezvous, or ownership transfer.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Branch (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentOfferCoverage
import Phil.Surface.GrammarV1.ComponentOfferReplay
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  accepted <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/accepted.phil"
  badBody <- TextIO.readFile "test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil"
  results <- sequence
    [ test "Go source-arm selection binds exact Core successor" (acceptedBranch accepted "Go" (Outcome "Done"))
    , test "Cancel source-arm selection binds exact Core successor" (acceptedBranch accepted "Cancel" (Outcome "Cancel"))
    , test "minimally rejected source arm body has exact class" (wrongBodyRejected badBody)
    , test "unlisted external selection fails before Core mutation" (unknownSelectionRejected accepted)
    , test "stale source endpoint has exact Core rejection" (staleEndpointRejected accepted)
    , test "mismatched projected session head fails closed" (wrongHeadRejected accepted)
    , test "wrong protocol instance never borrows projected authority" (wrongInstanceRejected accepted)
    , test "wrong endpoint role never borrows projected authority" (wrongRoleRejected accepted)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

data SourceOffer = SourceOffer
  { offerComponent :: GrammarV1ComponentDecl
  , offerInstance :: BinaryProtocolInstance
  , offerEndpoint :: Name
  }

serverRole :: ProtocolRoleKey
serverRole = ProtocolRoleKey "Server"

componentRoot :: DeclarationKey
componentRoot = DeclarationKey "component.ServerWorker"

sourceOffer :: Text.Text -> Either String SourceOffer
sourceOffer source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-source-offer-replay-v1" source)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  (protocol, component) <- case (protocols, components, programs) of
    ([p], [c], [_]) -> Right (p, c)
    _ -> Left "need one actual source protocol, component, and selected root"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.Choice")
      (InterfaceRevision "protocol.Choice.v1") protocol of
    Just (Right result) -> Right result
    other -> Left ("closed source protocol rejected: " <> show other)
  inst <- mapLeft show (instantiateBinaryProtocol strictGenericInstantiationPolicy family [] [])
  projection <- mapLeft show (projectProtocolRole inst serverRole)
  assert (protocolProjectionSession projection == Offer branches)
    "source protocol projected unexpected server head"
  checked <- case grammarV1CheckedComponentOfferCoverage
      componentRoot component (protocolProjectionSession projection) of
    Just (Right result) -> Right result
    other -> Left ("source arm coverage not checked: " <> show other)
  Right SourceOffer
    { offerComponent = component
    , offerInstance = inst
    , offerEndpoint = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint checked)
    }

initial :: SourceOffer -> Either String ProtocolContext
initial source = mapLeft show $
  insertProtocolEndpoint (offerEndpoint source)
    (binaryProtocolInstanceRevision (offerInstance source))
    serverRole (Offer branches) emptyProtocolContext

replay :: SourceOffer -> Text.Text -> Name -> ProtocolContext
       -> Either GrammarV1ComponentOfferReplayError GrammarV1ComponentOfferReplay
replay source label successor context =
  grammarV1ReplayComponentOffer componentRoot (offerComponent source)
    (offerInstance source) serverRole label successor context

acceptedBranch :: Text.Text -> Text.Text -> Outcome -> Either String ()
acceptedBranch input label outcome = do
  source <- sourceOffer input
  context <- initial source
  let endpoint = offerEndpoint source
      successor = Name ("source.replay." <> label)
      instRevision = binaryProtocolInstanceRevision (offerInstance source)
  result <- mapLeft show $ replay source label successor context
  let step = replayedComponentOfferStep result
      next = checkedProtocolContext step
  assert (replayedComponentOfferLabel result == label
       && grammarV1ResolvedBinderCoreName (replayedComponentOfferSourceEndpoint result) == endpoint
       && protocolProjectionInstance (replayedComponentOfferProjection result) == instRevision
       && protocolProjectionRole (replayedComponentOfferProjection result) == serverRole)
    "selected source arm or independently projected authority drifted"
  assert (protocolEndpointName (checkedProtocolPredecessor step) == endpoint
       && (protocolEndpointName <$> checkedProtocolSuccessor step) == Just successor
       && (protocolEndpointSession <$> checkedProtocolSuccessor step) == Just (End outcome)
       && (protocolEndpointInstance <$> checkedProtocolSuccessor step) == Just instRevision)
    "Core predecessor/successor or typed outcome drifted"
  assert (Map.notMember endpoint (protocolEndpoints next)
       && Map.notMember endpoint (linearBindings (protocolResources next))
       && Map.lookup successor (linearBindings (protocolResources next))
          == Just (TyEndpoint (End outcome)))
    "predecessor not consumed or exact typed successor absent"
  -- return unit in source does not itself close this endpoint.
  assert (Map.member successor (protocolEndpoints next))
    "replay silently discharged source endpoint's terminal obligation"

wrongBodyRejected :: Text.Text -> Either String ()
wrongBodyRejected input = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-rejected-body" input)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
            (grammarV1TopLevelDecls parsed)
      components = [c | GrammarV1ComponentDeclaration c <- top]
  component <- case components of
    [c] -> Right c
    _ -> Left "wrong-body fixture must parse to one actual component"
  case grammarV1CheckedComponentOfferCoverage componentRoot component (Offer branches) of
    Just (Left GrammarV1ComponentOfferArmBodyUnsupported) -> Right ()
    other -> Left ("wrong arm body not rejected by exact class: " <> show other)

unknownSelectionRejected :: Text.Text -> Either String ()
unknownSelectionRejected input = do
  source <- sourceOffer input
  context <- initial source
  case replay source "Ghost" (Name "new") context of
    Left (GrammarV1OfferReplayUnlistedLabel "Ghost") -> Right ()
    other -> Left ("external unlisted label admitted: " <> show other)

staleEndpointRejected :: Text.Text -> Either String ()
staleEndpointRejected input = do
  source <- sourceOffer input
  context <- initial source
  first <- mapLeft show (replay source "Go" (Name "new") context)
  case replay source "Go" (Name "another") (checkedProtocolContext (replayedComponentOfferStep first)) of
    Left (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown endpoint)) ->
      assert (endpoint == offerEndpoint source) "stale error lost exact source identity"
    other -> Left ("consumed source endpoint was accepted again: " <> show other)

wrongHeadRejected :: Text.Text -> Either String ()
wrongHeadRejected input = do
  source <- sourceOffer input
  let actualHead = Offer [head branches]
      expectedHead = Offer branches
  context <- mapLeft show $
    insertProtocolEndpoint (offerEndpoint source)
      (binaryProtocolInstanceRevision (offerInstance source))
      serverRole actualHead emptyProtocolContext
  case replay source "Go" (Name "new") context of
    Left (GrammarV1OfferReplayWrongLiveHead expected actual) ->
      assert (expected == expectedHead && actual == actualHead)
        "mismatched head did not report projected and actual session"
    other -> Left ("wrong live session head admitted: " <> show other)

wrongInstanceRejected :: Text.Text -> Either String ()
wrongInstanceRejected input = do
  source <- sourceOffer input
  let actual = ProtocolInstanceRevision "different.verified.instance"
      expected = binaryProtocolInstanceRevision (offerInstance source)
  context <- mapLeft show $
    insertProtocolEndpoint (offerEndpoint source) actual serverRole
      (Offer branches) emptyProtocolContext
  case replay source "Go" (Name "new") context of
    Left (GrammarV1OfferReplayProtocolError
      (ProtocolInstanceMismatch endpoint requested received)) ->
      assert (endpoint == offerEndpoint source && requested == expected && received == actual)
        "instance mismatch lost original projection/endpoint"
    other -> Left ("wrong instance was admitted: " <> show other)

wrongRoleRejected :: Text.Text -> Either String ()
wrongRoleRejected input = do
  source <- sourceOffer input
  let actual = ProtocolRoleKey "WrongServer"
  context <- mapLeft show $
    insertProtocolEndpoint (offerEndpoint source)
      (binaryProtocolInstanceRevision (offerInstance source))
      actual (Offer branches) emptyProtocolContext
  case replay source "Go" (Name "new") context of
    Left (GrammarV1OfferReplayProtocolError
      (ProtocolRoleMismatch endpoint requested received)) ->
      assert (endpoint == offerEndpoint source && requested == serverRole && received == actual)
        "role mismatch lost original projection/endpoint"
    other -> Left ("wrong role was admitted: " <> show other)

branches :: [Branch]
branches =
  [ Branch {branchLabel = "Go", branchPayload = Nothing,
            branchContinuation = End (Outcome "Done")}
  , Branch {branchLabel = "Cancel", branchPayload = Nothing,
            branchContinuation = End (Outcome "Cancel")}
  ]

assert :: Bool -> String -> Either String ()
assert ok explanation = if ok then Right () else Left explanation

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
