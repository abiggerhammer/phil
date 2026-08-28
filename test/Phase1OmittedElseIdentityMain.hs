{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( consumeLinear
  , insertBinding
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Outcome (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.Check.OmittedElse (checkOmittedElseIdentity)
import Phil.Surface.Check.Types
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-015 false arm is exact Unit-valued identity predecessor"
        falseIdentityIsExact
    , test "EXEC-015 compatible Unit true continuation joins with identity false"
        compatibleTrueJoins
    , test "EXEC-015 true-only linear consumption cannot weaken identity false"
        trueOnlyLinearConsumptionRejects
    , test "EXEC-015 non-Unit true continuation gets no invented false default"
        nonUnitTrueRejects
    , test "EXEC-015 residual obligations cannot disappear across identity false"
        obligationMismatchRejects
    , test "EXEC-015 unrestricted evidence cannot appear only on true continuation"
        evidenceMismatchRejects
    , test "EXEC-015 terminal true path leaves unchanged false continuation"
        terminalTrueLeavesIdentityFalse
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

falseIdentityIsExact :: Either String ()
falseIdentityIsExact = do
  paths <- mapLeft show $ checkOmittedElseIdentity testSpan baseState []
  case paths of
    [SurfacePath PathContinue state (Just RuntimeUnit)] ->
      assert (state == baseState)
        "omitted false predecessor changed incoming state"
    other -> Left ("unexpected omitted-else result: " <> show other)

compatibleTrueJoins :: Either String ()
compatibleTrueJoins = do
  let trueState = baseState { stateFresh = 7, stateFrame = 3 }
      truePath = SurfacePath PathContinue trueState (Just RuntimeUnit)
  paths <- mapLeft show $ checkOmittedElseIdentity testSpan baseState [truePath]
  case paths of
    [SurfacePath PathContinue state (Just RuntimeUnit)] -> do
      assert (resourceContext (stateCore state) == resourceContext (stateCore baseState))
        "compatible true join changed incoming resource state"
      assert (residualObligations (stateCore state) == residualObligations (stateCore baseState))
        "compatible true join changed incoming obligation state"
      assert (stateFresh state == 7 && stateFrame state == 3)
        "join failed to preserve ordinary freshness counters"
    other -> Left ("unexpected compatible join result: " <> show other)

trueOnlyLinearConsumptionRejects :: Either String ()
trueOnlyLinearConsumptionRejects = do
  incoming <- linearOwnerState
  trueState <- consumeOwner incoming
  let truePath = SurfacePath PathContinue trueState (Just RuntimeUnit)
  case checkOmittedElseIdentity testSpan incoming [truePath] of
    Left errorValue ->
      assert (surfaceErrorClass errorValue == IncompatibleBranchResidue)
        ("linear mismatch rejected at wrong layer: " <> show errorValue)
    Right paths -> Left
      ("true-only linear consumption was weakened at omitted else: " <> show paths)

nonUnitTrueRejects :: Either String ()
nonUnitTrueRejects =
  let value = RuntimeScalar (ScalarValue Unrestricted (TyUInt 8) PlainShape)
      truePath = SurfacePath PathContinue baseState (Just value)
  in case checkOmittedElseIdentity testSpan baseState [truePath] of
      Left errorValue ->
        assert (surfaceErrorClass errorValue == TypeMismatch)
          ("non-Unit true continuation rejected at wrong layer: " <> show errorValue)
      Right paths -> Left
        ("omitted else invented a false default for non-Unit result: " <> show paths)

obligationMismatchRejects :: Either String ()
obligationMismatchRejects =
  let obligation = Obligation
        { obligationId = ObligationId "exec015.pending"
        , obligationProposition = Truth
        , obligationOrigin = "exec015-fixture"
        , obligationScope = "true-arm"
        , obligationRequiredPoint = "conditional-join"
        }
      trueCore = (stateCore baseState)
        { residualObligations = Map.singleton (obligationId obligation) obligation }
      trueState = baseState { stateCore = trueCore }
      truePath = SurfacePath PathContinue trueState (Just RuntimeUnit)
  in case checkOmittedElseIdentity testSpan baseState [truePath] of
      Left errorValue ->
        assert (surfaceErrorClass errorValue == IncompatibleBranchResidue)
          ("obligation mismatch rejected at wrong layer: " <> show errorValue)
      Right paths -> Left
        ("true-only residual obligation crossed identity false: " <> show paths)

evidenceMismatchRejects :: Either String ()
evidenceMismatchRejects = do
  trueContext <- mapLeft show $
    insertBinding
      Unrestricted
      (Name "trueEvidence")
      (TyProof Truth)
      (resourceContext (stateCore baseState))
  let evidenceMeta = BindingMeta Unrestricted (TyProof Truth) PlainShape
      trueState = baseState
        { stateCore = (stateCore baseState) { resourceContext = trueContext }
        , stateBindings = Map.singleton "trueEvidence" evidenceMeta
        }
      truePath = SurfacePath PathContinue trueState (Just RuntimeUnit)
  case checkOmittedElseIdentity testSpan baseState [truePath] of
    Left errorValue ->
      assert (surfaceErrorClass errorValue == IncompatibleBranchResidue)
        ("evidence mismatch rejected at wrong layer: " <> show errorValue)
    Right paths -> Left
      ("true-only unrestricted evidence crossed identity false: " <> show paths)

terminalTrueLeavesIdentityFalse :: Either String ()
terminalTrueLeavesIdentityFalse = do
  let terminal = SurfacePath
        (PathClosed (Outcome "done"))
        baseState
        Nothing
  paths <- mapLeft show $ checkOmittedElseIdentity testSpan baseState [terminal]
  case paths of
    [ actualTerminal
      , SurfacePath PathContinue falseState (Just RuntimeUnit)
      ] -> do
        assert (actualTerminal == terminal)
          "terminal true path was rewritten"
        assert (falseState == baseState)
          "terminal true path changed the false identity continuation"
    other -> Left ("unexpected terminal/identity result: " <> show other)

baseState :: SurfaceState
baseState = SurfaceState
  { stateCore = emptyCheckState
  , stateBindings = Map.empty
  , stateFresh = 0
  , stateFrame = 0
  , stateActiveEndpoint = Nothing
  }

linearOwnerState :: Either String SurfaceState
linearOwnerState = do
  context <- mapLeft show $
    insertBinding Linear (Name "owner") ownerTy (resourceContext emptyCheckState)
  Right baseState
    { stateCore = emptyCheckState { resourceContext = context }
    , stateBindings = Map.singleton "owner" ownerMeta
    }

consumeOwner :: SurfaceState -> Either String SurfaceState
consumeOwner state = do
  (_, context) <- mapLeft show $
    consumeLinear (Name "owner") (resourceContext (stateCore state))
  Right state
    { stateCore = (stateCore state) { resourceContext = context }
    , stateBindings = Map.delete "owner" (stateBindings state)
    }

ownerTy :: Ty
ownerTy = TyOpaque "Owner"

ownerMeta :: BindingMeta
ownerMeta = BindingMeta Linear ownerTy PlainShape

testSpan :: SourceSpan
testSpan = SourceSpan
  (SourcePoint "exec015" 1 1 0)
  (SourcePoint "exec015" 1 20 19)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
