{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.CallableOutcomeBranchResourceApply
  ( applySurfaceCallableOutcomeResourceResidue
  )
import Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  )
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome (CallableOutcomeState (..))
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( ResourceContext (..)
  , joinContinuing
  )
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceShape (..)
  , SurfaceState (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 applies matching resource residue without disturbing unrelated state"
        matchingResiduePreservesUnmentioned
    , test "CALL-019 ordinary join accepts equal applied linear residue"
        equalResidueJoins
    , test "CALL-019 ordinary join rejects sibling linear residue mismatch"
        mismatchedResidueRejectsAtOrdinaryJoin
    , test "CALL-019 exact successor metadata replaces predecessor occurrence"
        successorReplacementIsExact
    , test "CALL-019 active endpoint residue must name a live endpoint"
        invalidActiveEndpointRejects
    , test "CALL-019 active endpoint residue is restored exactly"
        activeEndpointRestored
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

span' :: SourceSpan
span' = SourceSpan
  (SourcePoint "call019-resource-apply" 1 1 0)
  (SourcePoint "call019-resource-apply" 1 2 1)

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

ownerMeta, successorMeta, tagMeta, endpointMeta :: BindingMeta
ownerMeta = BindingMeta Linear (TyOpaque "Owner") PlainShape
successorMeta = BindingMeta Linear (TyOpaque "SuccessorOwner") PlainShape
tagMeta = BindingMeta Unrestricted (TyOpaque "Tag") PlainShape
endpointMeta = BindingMeta Linear (TyEndpoint (End (Outcome "done"))) PlainShape

baseState :: Either String SurfaceState
baseState = do
  owner <- mapLeft show $ insertBindingMeta span' "owner" ownerMeta emptySurfaceState
  mapLeft show $ insertBindingMeta span' "tag" tagMeta owner

residue
  :: String
  -> Map.Map Text SurfaceCallableOutcomeResourceExpectation
  -> Maybe Text
  -> SurfaceCallableOutcomeResourceResidueBinding
residue label bindings active = SurfaceCallableOutcomeResourceResidueBinding
  { surfaceOutcomeResourceInvocationSpan = span'
  , surfaceOutcomeResourceDeclarationKey = workerKey
  , surfaceOutcomeResourceSourceLabel = Text.pack label
  , surfaceOutcomeResourceState = CallableOutcomeState (Text.pack ("state." <> label))
  , surfaceOutcomeResourceCalleeTransition = PreserveCallee
  , surfaceOutcomeResourceBindings = bindings
  , surfaceOutcomeResourceActiveEndpoint = active
  }

presentOwner :: String -> SurfaceCallableOutcomeResourceResidueBinding
presentOwner label = residue label
  (Map.singleton "owner" (SurfaceCallableResourcePresent ownerMeta))
  Nothing

absentOwner :: String -> SurfaceCallableOutcomeResourceResidueBinding
absentOwner label = residue label
  (Map.singleton "owner" SurfaceCallableResourceAbsent)
  Nothing

matchingResiduePreservesUnmentioned :: Either String ()
matchingResiduePreservesUnmentioned = do
  initial <- baseState
  applied <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' (presentOwner "ok") initial
  assert (Map.lookup "owner" (stateBindings applied) == Just ownerMeta)
    "owner metadata changed"
  assert (Map.lookup "tag" (stateBindings applied) == Just tagMeta)
    "unmentioned unrestricted binding changed"
  let context = resourceContext (stateCore applied)
  assert (Map.member (Name "owner") (linearBindings context))
    "owner disappeared from linear Core zone"
  assert (Map.member (Name "tag") (unrestrictedBindings context))
    "unmentioned tag disappeared from Core zone"

equalResidueJoins :: Either String ()
equalResidueJoins = do
  initial <- baseState
  left <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' (presentOwner "ok") initial
  right <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' (presentOwner "retry") initial
  joined <- mapLeft show $
    joinContinuing
      [ resourceContext (stateCore left)
      , resourceContext (stateCore right)
      ]
  assert (Map.member (Name "owner") (linearBindings joined))
    "ordinary join dropped equal linear residue"

mismatchedResidueRejectsAtOrdinaryJoin :: Either String ()
mismatchedResidueRejectsAtOrdinaryJoin = do
  initial <- baseState
  left <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' (presentOwner "ok") initial
  right <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' (absentOwner "retry") initial
  case joinContinuing
      [ resourceContext (stateCore left)
      , resourceContext (stateCore right)
      ] of
    Left _ -> Right ()
    Right joined -> Left ("incompatible sibling residue joined: " <> show joined)

successorReplacementIsExact :: Either String ()
successorReplacementIsExact = do
  initial <- baseState
  let replacement = residue "ok"
        (Map.singleton "owner" (SurfaceCallableResourcePresent successorMeta))
        Nothing
  applied <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' replacement initial
  assert (Map.lookup "owner" (stateBindings applied) == Just successorMeta)
    "successor metadata did not replace predecessor"
  let context = resourceContext (stateCore applied)
  assert (Map.lookup (Name "owner") (linearBindings context)
      == Just (bindingType successorMeta))
    "Core linear zone did not receive exact successor type"

invalidActiveEndpointRejects :: Either String ()
invalidActiveEndpointRejects = do
  initial <- baseState
  let invalid = residue "ok"
        (Map.singleton "owner" (SurfaceCallableResourcePresent ownerMeta))
        (Just "owner")
  case applySurfaceCallableOutcomeResourceResidue span' invalid initial of
    Left errorValue
      | surfaceErrorClass errorValue == IncompatibleBranchResidue -> Right ()
    Left other -> Left ("wrong active-endpoint rejection: " <> show other)
    Right accepted -> Left ("non-endpoint accepted as active endpoint: " <> show accepted)

activeEndpointRestored :: Either String ()
activeEndpointRestored = do
  initial <- baseState
  let withEndpoint = residue "ok"
        (Map.fromList
          [ ("owner", SurfaceCallableResourcePresent ownerMeta)
          , ("ep", SurfaceCallableResourcePresent endpointMeta)
          ])
        (Just "ep")
  applied <- mapLeft show $
    applySurfaceCallableOutcomeResourceResidue span' withEndpoint initial
  assert (stateActiveEndpoint applied == Just "ep")
    "active endpoint residue was not restored"
  assert (Map.lookup "ep" (stateBindings applied) == Just endpointMeta)
    "endpoint metadata was not installed"

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
