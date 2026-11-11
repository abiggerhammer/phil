{-# LANGUAGE OverloadedStrings #-}

-- FSEM-02: differential replay of two separately parsed, fully source-checked
-- offer-arm orders against the SAME admitted protocol projection and Core
-- state. No source-derived activation, peer End authority, or Rocq refinement.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context (CheckError (..), ResourceContext (..), insertBinding, startSharedLoan)
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Session (SessionError (..))
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Core.Syntax (Branch (..), Mode (..), Name (..), Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.ComponentOfferCoverage
import Phil.Surface.GrammarV1.ComponentOfferReplay
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles (grammarV1ClosedBinaryProtocolFamily)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  original <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/accepted.phil"
  permuted <- TextIO.readFile "test/fixtures/fsem02-offer-arm-order-v1/reordered.phil"
  duplicate <- TextIO.readFile "test/fixtures/fsem02-source-offer-v1/duplicate-arm.phil"
  missing <- TextIO.readFile "test/fixtures/fsem02-branch-outcome-separation-v1/missing-cancel.phil"
  results <- sequence
    [ test "separate checked offer sources retain different arm orders" (ordersAccepted original permuted)
    , test "Go/Done choice is invariant under checked source arm order" (sameBranchReplay original permuted "Go" (Outcome "Done"))
    , test "Cancel/Cancel choice is invariant under checked source arm order" (sameBranchReplay original permuted "Cancel" (Outcome "Cancel"))
    , test "duplicate source arm rejects exactly, not last/first wins" (duplicateRejected duplicate)
    , test "permuted offer cannot replay a consumed predecessor" (staleRejected original permuted)
    , test "permuted source cannot justify an unprojected live head" (wrongHeadRejected permuted)
    , test "distinct source-selected branches separate End outcomes at one original Core state" (crossBranchIsolation original)
    , test "one missing source branch rejects by exact class" (missingArmRejected missing)
    , test "Go/Cancel reject occupied successor names in every resource mode" (occupiedSuccessorRejected original)
    , test "Go/Cancel reject successor equal to the source predecessor" (reusedPredecessorRejected original)
    , test "Go/Cancel and authorized End closes preserve a borrowed affine spectator" (borrowedSpectatorFrame original)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

data SourcePlan = SourcePlan
  { planComponent :: GrammarV1ComponentDecl
  , planInstance :: BinaryProtocolInstance
  , planProjection :: Session
  }

root :: DeclarationKey
root = DeclarationKey "component.ServerWorker"

serverRole :: ProtocolRoleKey
serverRole = ProtocolRoleKey "Server"

sourcePlan :: Text.Text -> Either String SourcePlan
sourcePlan source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource "fsem02-offer-order" source)
  let top = map (locatedValue . grammarV1Declaration . locatedValue)
              (grammarV1TopLevelDecls parsed)
      protocols = [p | GrammarV1ProtocolDeclaration p <- top]
      components = [c | GrammarV1ComponentDeclaration c <- top]
      programs = [p | GrammarV1ProgramDeclaration p <- top]
  (protocol, component) <- case (protocols, components, programs) of
    ([p], [c], [_]) -> Right (p, c)
    _ -> Left "complete checked source must contain one protocol, component and root"
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.Choice")
      (InterfaceRevision "protocol.Choice.v1") protocol of
    Just (Right checkedFamily) -> Right checkedFamily
    other -> Left ("not a checked binary source protocol: " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  server <- mapLeft show $ projectProtocolRole instanceValue serverRole
  assert (protocolProjectionSession server == expectedHead)
    "actual source protocol projection does not have the admitted two-branch head"
  pure SourcePlan
    { planComponent = component
    , planInstance = instanceValue
    , planProjection = protocolProjectionSession server
    }

checked :: SourcePlan -> Either String GrammarV1CheckedComponentOfferCoverage
checked source =
  case grammarV1CheckedComponentOfferCoverage
      root (planComponent source) (planProjection source) of
    Just (Right result) -> Right result
    other -> Left ("source offer arm coverage failed: " <> show other)

pair :: Text.Text -> Text.Text
     -> Either String (SourcePlan, GrammarV1CheckedComponentOfferCoverage,
                       SourcePlan, GrammarV1CheckedComponentOfferCoverage)
pair first second = do
  a <- sourcePlan first
  b <- sourcePlan second
  ca <- checked a
  cb <- checked b
  assert (binaryProtocolInstanceRevision (planInstance a)
       == binaryProtocolInstanceRevision (planInstance b))
    "separately checked source projections have distinct protocol identities"
  assert (planProjection a == planProjection b)
    "source arm permutation silently changed the checked role continuation catalog"
  assert (grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint ca)
       == grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint cb))
    "source arm permutation changed the source-resolved parameter occurrence"
  pure (a, ca, b, cb)

ordersAccepted :: Text.Text -> Text.Text -> Either String ()
ordersAccepted first second = do
  (_, ca, _, cb) <- pair first second
  assert (checkedComponentOfferLabels ca == ["Go", "Cancel"]
       && checkedComponentOfferLabels cb == ["Cancel", "Go"])
    "source arm order was not independently checked in both complete programs"

replay :: SourcePlan -> Text.Text -> Name -> ProtocolContext
       -> Either GrammarV1ComponentOfferReplayError GrammarV1ComponentOfferReplay
replay source label next =
  grammarV1ReplayComponentOffer root (planComponent source)
    (planInstance source) serverRole label next

initial :: SourcePlan -> Name -> Session -> Either String ProtocolContext
initial source endpoint headSession = mapLeft show $
  insertProtocolEndpoint endpoint
    (binaryProtocolInstanceRevision (planInstance source))
    serverRole headSession emptyProtocolContext

sameBranchReplay :: Text.Text -> Text.Text -> Text.Text -> Outcome -> Either String ()
sameBranchReplay first second label outcome = do
  (a, ca, b, _) <- pair first second
  let predecessor = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint ca)
      successor = Name ("fsem02.permutation." <> label)
      revision = binaryProtocolInstanceRevision (planInstance a)
  before <- initial a predecessor expectedHead
  firstStep <- mapLeft show $ replay a label successor before
  secondStep <- mapLeft show $ replay b label successor before
  let lhs = replayedComponentOfferStep firstStep
      rhs = replayedComponentOfferStep secondStep
      after = checkedProtocolContext lhs
  assert (checkedProtocolPredecessor lhs == checkedProtocolPredecessor rhs
       && checkedProtocolSuccessor lhs == checkedProtocolSuccessor rhs
       && after == checkedProtocolContext rhs)
    "independently executed source choices diverged on a complete Core step"
  assert (Map.notMember predecessor (protocolEndpoints after)
       && Map.notMember predecessor (linearBindings (protocolResources after))
       && Map.lookup successor (linearBindings (protocolResources after))
            == Just (TyEndpoint (End outcome)))
    "the two source orders did not consume and type the same exact successor"
  assert ((protocolEndpointSession <$> checkedProtocolSuccessor lhs) == Just (End outcome))
    "selected branch got the other label's End outcome"
  closedA <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest successor revision serverRole outcome) after
  closedB <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest successor revision serverRole outcome)
    (checkedProtocolContext rhs)
  assert (checkedProtocolSuccessor closedA == Nothing
       && checkedProtocolContext closedA == checkedProtocolContext closedB
       && Map.null (protocolEndpoints (checkedProtocolContext closedA)))
    "authorized terminal Core replay diverged or manufactured a successor"

duplicateRejected :: Text.Text -> Either String ()
duplicateRejected source = do
  plan <- sourcePlan source
  case grammarV1CheckedComponentOfferCoverage root
      (planComponent plan) (planProjection plan) of
    Just (Left (GrammarV1ComponentOfferDuplicateArm label)) ->
      assert (label == "Go") "duplicate source label diagnostic lost exact name"
    other -> Left ("duplicate offer arm was not rejected exactly: " <> show other)

staleRejected :: Text.Text -> Text.Text -> Either String ()
staleRejected first second = do
  (a, ca, b, _) <- pair first second
  let old = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint ca)
      next = Name "fsem02.once"
  before <- initial a old expectedHead
  stepped <- mapLeft show $ replay a "Go" next before
  case replay b "Go" (Name "fsem02.twice")
      (checkedProtocolContext (replayedComponentOfferStep stepped)) of
    Left (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown absent)) ->
      assert (absent == old) "stale replay lost the original source binder identity"
    other -> Left ("permuted source revived an already consumed endpoint: " <> show other)

wrongHeadRejected :: Text.Text -> Either String ()
wrongHeadRejected source = do
  plan <- sourcePlan source
  coverage <- checked plan
  let old = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint coverage)
      actual = End (Outcome "Done")
  before <- initial plan old actual
  case replay plan "Go" (Name "fsem02.wrong-head") before of
    Left (GrammarV1OfferReplayWrongLiveHead expected observed) ->
      assert (expected == expectedHead && observed == actual)
        "wrong-head rejection lost the projected/actual sessions"
    other -> Left ("source arm order authorized a wrong live protocol head: " <> show other)


-- Reexecute TWO DIFFERENT source-covered choices from the exact SAME original
-- Core endpoint state. They share a fresh successor name only because these
-- are disjoint hypothetical executions, never simultaneously live outcomes.
-- Each branch must keep its own End type, reject the other's close outcome,
-- and refuse a replay on a predecessor already consumed in that branch.
crossBranchIsolation :: Text.Text -> Either String ()
crossBranchIsolation source = do
  plan <- sourcePlan source
  coverage <- checked plan
  let predecessor = grammarV1ResolvedBinderCoreName
        (checkedComponentOfferEndpoint coverage)
      successor = Name "fsem02.branch.separate"
      revision = binaryProtocolInstanceRevision (planInstance plan)
      done = Outcome "Done"
      canceled = Outcome "Cancel"
  before <- initial plan predecessor expectedHead
  go <- mapLeft show $ replay plan "Go" successor before
  cancel <- mapLeft show $ replay plan "Cancel" successor before
  let goStep = replayedComponentOfferStep go
      cancelStep = replayedComponentOfferStep cancel
      goContext = checkedProtocolContext goStep
      cancelContext = checkedProtocolContext cancelStep
      goResources = protocolResources goContext
      cancelResources = protocolResources cancelContext
  assert (checkedProtocolPredecessor goStep
       == checkedProtocolPredecessor cancelStep
       && checkedProtocolContext goStep /= checkedProtocolContext cancelStep)
    "two independent source branch choices collapsed to one identical Core state"
  assert (Map.notMember predecessor (protocolEndpoints goContext)
       && Map.notMember predecessor (protocolEndpoints cancelContext)
       && Map.notMember predecessor (linearBindings goResources)
       && Map.notMember predecessor (linearBindings cancelResources))
    "a branch replay retained its consumed predecessor"
  assert (Map.lookup successor (linearBindings goResources)
            == Just (TyEndpoint (End done))
       && Map.lookup successor (linearBindings cancelResources)
            == Just (TyEndpoint (End canceled))
       && (protocolEndpointSession <$> checkedProtocolSuccessor goStep)
            == Just (End done)
       && (protocolEndpointSession <$> checkedProtocolSuccessor cancelStep)
            == Just (End canceled))
    "selected source labels did not preserve distinct exact typed End heads"
  case checkProtocolAction
      (ProtocolCloseRequest successor revision serverRole canceled) goContext of
    Left (ProtocolSessionError (CloseOutcomeMismatch expected observed)) ->
      assert (expected == done && observed == canceled)
        "Go chosen head lost its exact rejected cross-branch close outcomes"
    other -> Left ("Go branch accepted a Cancel End close: " <> show other)
  case checkProtocolAction
      (ProtocolCloseRequest successor revision serverRole done) cancelContext of
    Left (ProtocolSessionError (CloseOutcomeMismatch expected observed)) ->
      assert (expected == canceled && observed == done)
        "Cancel chosen head lost its exact rejected cross-branch close outcomes"
    other -> Left ("Cancel branch accepted a Go End close: " <> show other)
  case replay plan "Cancel" (Name "fsem02.second-branch") goContext of
    Left (GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown stale)) ->
      assert (stale == predecessor)
        "cross-branch replay did not identify the consumed source predecessor"
    other -> Left ("cross-branch replay revived a consumed owner: " <> show other)
  closedGo <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest successor revision serverRole done) goContext
  closedCancel <- mapLeft show $ checkProtocolAction
    (ProtocolCloseRequest successor revision serverRole canceled) cancelContext
  assert (checkedProtocolSuccessor closedGo == Nothing
       && checkedProtocolSuccessor closedCancel == Nothing
       && checkedProtocolContext closedGo == checkedProtocolContext closedCancel
       && checkedProtocolContext closedGo == emptyProtocolContext)
    "separate authorized End closes did not restore the SAME original empty state"


-- A successor name occupied by ANY structural-mode owner is not fresh.
-- These are independently executed source-covered choices, not manual
-- substitutions into a successful step. The exact nested production error
-- must identify the collision and must not produce a post-error context.
occupiedSuccessorRejected :: Text.Text -> Either String ()
occupiedSuccessorRejected source = do
  plan <- sourcePlan source
  coverage <- checked plan
  let old = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint coverage)
      occupied = Name "fsem02.occupied.successor"
  before <- initial plan old expectedHead
  mapM_ (checkMode plan occupied before) [Unrestricted, Affine, Linear]
  where
    checkMode plan occupied before mode = do
      resources <- mapLeft show $
        insertBinding mode occupied TyUnit (protocolResources before)
      let withSpectator = before { protocolResources = resources }
      mapM_ (rejectChoice plan occupied withSpectator mode) ["Go", "Cancel"]
    rejectChoice plan occupied withSpectator mode label =
      case replay plan label occupied withSpectator of
        Left (GrammarV1OfferReplayProtocolError
                (ProtocolSessionError
                  (SessionResourceError (DuplicateBinding collision)))) ->
          assert (collision == occupied)
            ("collision in " <> show mode <> " lost the spectator name")
        other -> Left ("source-offer " <> show label <> " with occupied " <>
                        show mode <> " successor did not reject exactly: " <> show other)

reusedPredecessorRejected :: Text.Text -> Either String ()
reusedPredecessorRejected source = do
  plan <- sourcePlan source
  coverage <- checked plan
  let old = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint coverage)
  before <- initial plan old expectedHead
  mapM_ (rejectSame plan old before) ["Go", "Cancel"]
  where
    rejectSame plan old before label =
      case replay plan label old before of
        Left (GrammarV1OfferReplayProtocolError
                (ProtocolSessionError (SuccessorReusesEndpointName name))) ->
          assert (name == old) "same-name rejection lost the exact source predecessor"
        other -> Left ("same-name source offer incorrectly progressed " <>
                       show label <> ": " <> show other)

-- The source-replayed local offer and its separately authorized End close
-- leave an unrelated borrowed affine owner untouched, including its loan
-- token. The loan is an explicit Core premise, not inferred from the source.
borrowedSpectatorFrame :: Text.Text -> Either String ()
borrowedSpectatorFrame source = do
  plan <- sourcePlan source
  coverage <- checked plan
  let predecessor = grammarV1ResolvedBinderCoreName (checkedComponentOfferEndpoint coverage)
      spectator = Name "fsem02.borrowed.spectator"
      next = Name "fsem02.fresh.endpoint"
      revision = binaryProtocolInstanceRevision (planInstance plan)
  before <- initial plan predecessor expectedHead
  framed <- mapLeft show $ insertBinding Affine spectator TyUnit (protocolResources before)
  loaned <- mapLeft show $ startSharedLoan spectator framed
  let withSpectator = before { protocolResources = loaned }
  mapM_ (checkFrame plan next revision withSpectator spectator)
    [("Go", Outcome "Done"), ("Cancel", Outcome "Cancel")]
  where
    checkFrame plan next revision withSpectator spectator (label, outcome) = do
      offer <- mapLeft show $ replay plan label next withSpectator
      let after = checkedProtocolContext (replayedComponentOfferStep offer)
      assert (Map.lookup spectator (affineBindings (protocolResources after))
                == Just TyUnit
           && protocolResources after == (protocolResources withSpectator)
              { linearBindings = linearBindings (protocolResources after) }
           && Map.lookup spectator (protocolEndpoints after) == Nothing)
        ("offer " <> show label <> " modified the independent borrowed spectator")
      close <- mapLeft show $ checkProtocolAction
        (ProtocolCloseRequest next revision serverRole outcome) after
      assert (checkedProtocolSuccessor close == Nothing
           && checkedProtocolContext close == withSpectator
                { protocolResources = (protocolResources withSpectator)
                    { linearBindings = Map.delete
                        (checkedProtocolPredecessorName offer)
                        (linearBindings (protocolResources withSpectator)) } })
        ("authorized End close on " <> show label <>
          " did not return exactly to the borrowed spectator frame")

checkedProtocolPredecessorName :: GrammarV1ComponentOfferReplay -> Name
checkedProtocolPredecessorName =
  protocolEndpointName . checkedProtocolPredecessor . replayedComponentOfferStep

missingArmRejected :: Text.Text -> Either String ()
missingArmRejected source = do
  plan <- sourcePlan source
  case grammarV1CheckedComponentOfferCoverage root
      (planComponent plan) (planProjection plan) of
    Just (Left (GrammarV1ComponentOfferMissingArm label)) ->
      assert (label == "Cancel") "missing-arm rejection lost the source label"
    other -> Left ("missing source arm was not rejected exactly: " <> show other)

expectedHead :: Session
expectedHead = Offer
  [ Branch { branchLabel = "Go", branchPayload = Nothing,
             branchContinuation = End (Outcome "Done") }
  , Branch { branchLabel = "Cancel", branchPayload = Nothing,
             branchContinuation = End (Outcome "Cancel") }
  ]

assert :: Bool -> String -> Either String ()
assert ok explanation = if ok then Right () else Left explanation

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
