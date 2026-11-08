{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02 source offer coverage and Core-only branch progression.
-- No universal source/implementation refinement or rendezvous is asserted.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Session (SessionError (..), SessionAction (..))
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Branch (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentOfferCoverage
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  accepted <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/accepted.phil"
  missing <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/missing-arm.phil"
  duplicate <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/duplicate-arm.phil"
  unknown <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/unknown-operand.phil"
  results <- sequence
    [ test "source offer is total for checked role projection" (acceptedOffer accepted)
    , test "source missing arm rejects exact missing label" (missingOfferRejected missing)
    , test "duplicate arm rejects exact source label" (duplicateOfferRejected duplicate)
    , test "nonlocal source offer operand never admits protocol identity" (unknownOperandRejected unknown)
    , test "wrong projection head rejects before any offer progression" (wrongHeadRejected accepted)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

data SourceOffer = SourceOffer
  { offerComponent :: GrammarV1ComponentDecl
  , offerInstance :: ProtocolInstanceRevision
  , offerProjection :: ProtocolProjectionEvidence
  , selectProjection :: ProtocolProjectionEvidence
  }

sourceOffer :: Text.Text -> Either String SourceOffer
sourceOffer source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-source-offer-v1" source)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  (protocol, component) <- case (protocols, components, programs) of
    ([p], [c], [_]) -> Right (p, c)
    _ -> Left "source offer requires protocol, component and selected program root"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.Choice")
      (InterfaceRevision "protocol.Choice.v1") protocol of
    Just (Right result) -> Right result
    other -> Left ("source offer protocol projection rejected: " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  server <- mapLeft show $ projectProtocolRole instanceValue serverRole
  client <- mapLeft show $ projectProtocolRole instanceValue clientRole
  assert (protocolProjectionSession server == Offer branches
       && protocolProjectionSession client == Select branches)
    "source family failed exact closed dual head projection"
  Right SourceOffer
    { offerComponent = component
    , offerInstance = binaryProtocolInstanceRevision instanceValue
    , offerProjection = server
    , selectProjection = client
    }

checked :: SourceOffer
  -> Either String GrammarV1CheckedComponentOfferCoverage
checked source = case grammarV1CheckedComponentOfferCoverage
    (DeclarationKey "component.ServerWorker")
    (offerComponent source) (offerProjection source) of
  Just (Right result) -> Right result
  other -> Left ("source offer not checked: " <> show other)

acceptedOffer :: Text.Text -> Either String ()
acceptedOffer input = do
  source <- sourceOffer input
  result <- checked source
  assert (checkedComponentOfferLabels result == ["Go", "Cancel"])
    "actual source arm order or labels drifted"
  let endpoint = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint result)
      instanceRevision = offerInstance source
  mapM_ (checkBranch endpoint instanceRevision) [("Go", Outcome "Done"),("Cancel", Outcome "Cancel")]
  where
    checkBranch endpoint instanceRevision (label, outcome) = do
      let successor = Name ("core.verified.offer." <> label)
      initial <- mapLeft show $
        insertProtocolEndpoint endpoint instanceRevision serverRole
          (Offer branches) emptyProtocolContext
      stepped <- mapLeft show $ checkProtocolAction
        (ProtocolOfferRequest endpoint successor instanceRevision serverRole label) initial
      let next = checkedProtocolContext stepped
      continuation = checkedProtocolSuccessor stepped
      assert (protocolEndpointName <$> continuation == Just successor
           && protocolEndpointSession <$> continuation == Just (End outcome)
           && protocolEndpointInstance <$> continuation == Just instanceRevision
           && protocolEndpointRole <$> continuation == Just serverRole)
        "offer lost source branch or exact successor contract"
      assert (Map.notMember endpoint (protocolEndpoints next)
           && Map.notMember endpoint (linearBindings (protocolResources next))
           && Map.lookup successor (linearBindings (protocolResources next))
                == Just (TyEndpoint (End outcome)))
        "offer did not consume old endpoint and bind typed successor"
      case checkProtocolAction
        (ProtocolOfferRequest endpoint (Name "core.stale") instanceRevision serverRole label) next of
        Left (ProtocolEndpointUnknown stale) ->
          assert (stale == endpoint) "stale endpoint diagnostic changed"
        other -> Left ("stale endpoint replay succeeded: " <> show other)
      closed <- mapLeft show $ checkProtocolAction
        (ProtocolCloseRequest successor instanceRevision serverRole outcome) next
      assert (Map.null (protocolEndpoints (checkedProtocolContext closed))
           && Map.null (linearBindings (protocolResources (checkedProtocolContext closed))))
        "terminal close retained protocol endpoint or linear ownership"

missingOfferRejected :: Text.Text -> Either String ()
missingOfferRejected input = do
  source <- sourceOffer input
  case grammarV1CheckedComponentOfferCoverage
    (DeclarationKey "component.ServerWorker") (offerComponent source) (offerProjection source) of
    Just (Left (GrammarV1ComponentOfferMissingArm label)) ->
      assert (label == "Cancel") "missing-arm class changed"
    other -> Left ("missing source branch was admitted: " <> show other)

duplicateOfferRejected :: Text.Text -> Either String ()
duplicateOfferRejected input = do
  source <- sourceOffer input
  case grammarV1CheckedComponentOfferCoverage
    (DeclarationKey "component.ServerWorker") (offerComponent source) (offerProjection source) of
    Just (Left (GrammarV1ComponentOfferDuplicateArm label)) ->
      assert (label == "Go") "duplicate-arm class changed"
    other -> Left ("duplicate source branch was admitted: " <> show other)

unknownOperandRejected :: Text.Text -> Either String ()
unknownOperandRejected input = do
  source <- sourceOffer input
  case grammarV1CheckedComponentOfferCoverage
    (DeclarationKey "component.ServerWorker") (offerComponent source) (offerProjection source) of
    Just (Left GrammarV1ComponentOfferOperandNotLocal) -> Right ()
    other -> Left ("unbound offer scrutinee was admitted: " <> show other)

wrongHeadRejected :: Text.Text -> Either String ()
wrongHeadRejected input = do
  source <- sourceOffer input
  case grammarV1CheckedComponentOfferCoverage
    (DeclarationKey "component.ServerWorker") (offerComponent source) (selectProjection source) of
    Just (Left (GrammarV1ComponentOfferWrongSessionHead (Select actual))) ->
      assert (actual == branches) "wrong-head rejection lost actual projected state"
    other -> Left ("source offer accepted select head: " <> show other)

branches :: [Branch]
branches =
  [ Branch {branchLabel = "Go", branchPayload = Nothing,
            branchContinuation = End (Outcome "Done")}
  , Branch {branchLabel = "Cancel", branchPayload = Nothing,
            branchContinuation = End (Outcome "Cancel")}
  ]

clientRole, serverRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"
serverRole = ProtocolRoleKey "Server"

assert :: Bool -> String -> Either String ()
assert ok explanation = if ok then Right () else Left explanation

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
