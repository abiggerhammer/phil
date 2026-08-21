{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeAffine
  , consumeLinear
  , emptyContext
  , insertBinding
  , startSharedLoan
  )
import Phil.Core.Process
  ( FlowPath
  , ProcessError (..)
  , ProcessFlow
  , closedFlow
  , continueFlow
  , failedFlow
  , flowPaths
  , joinBranches
  , pathControl
  , pathState
  , returnFlow
  , sequenceFlow
  )
import Phil.Core.Syntax
  ( Control (..)
  , Mode (..)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , Proposition (Atom)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Continue executes sequential continuation" testContinueSequences
    , test "Return short-circuits sequential continuation and carries linear residue" testReturnShortCircuits
    , test "Return rejects an escaping shared loan" testReturnRejectsLoan
    , test "Closed rejects undisposed linear resources" testClosedRejectsLinear
    , test "Failed rejects undisposed linear resources" testFailedRejectsLinear
    , test "Closed and Failed short-circuit sequential continuation" testTerminalShortCircuits
    , test "terminal branch is excluded from continuing resource join" testTerminalBranchExcluded
    , test "incompatible continuing branches still fail to join" testContinuingMismatch
    , test "mixed Return/Continue branches preserve both paths" testMixedReturnContinue
    , test "all-terminal branch creates no fake continuing path" testAllTerminal
    , test "affine weakening is normalized across continuing branch paths" testAffineJoinNormalizes
    , test "branch-local obligations remain path-sensitive after join" testPathSensitiveObligations
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

nty :: Text -> Ty
nty = TyOpaque

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testContinueSequences :: Either String ()
testContinueSequences = do
  context0 <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  let initial = continueFlow (withContext context0)
  result <- mapLeft show $ sequenceFlow initial consumeCap
  path <- solePath result
  assert (pathControl path == Continue) "continuing sequence changed control result"
  assert
    (Map.null (affineBindings (resourceContext (pathState path))))
    "sequential continuation did not receive and update the prior residual context"
  where
    consumeCap state =
      case consumeAffine (name "cap") (resourceContext state) of
        Left err -> Left (BranchJoinError err)
        Right (_, context) -> Right (continueFlow state { resourceContext = context })

testReturnShortCircuits :: Either String ()
testReturnShortCircuits = do
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  returning <- mapLeft show $ returnFlow TyUnit (withContext context)
  result <- mapLeft show $ sequenceFlow returning (const (Left EmptyBranchSet))
  path <- solePath result
  assert (pathControl path == Return TyUnit) "return control was not preserved"
  assert
    (Map.member (name "endpoint") (linearBindings (resourceContext (pathState path))))
    "return path lost its residual linear resource"

testReturnRejectsLoan :: Either String ()
testReturnRejectsLoan = do
  context0 <- mapLeft show $ insertBinding Linear (name "payload") (nty "OwnedBytes") emptyContext
  context1 <- mapLeft show $ startSharedLoan (name "payload") context0
  case returnFlow TyUnit (withContext context1) of
    Left (InvalidReturnState (EscapingLoans loans)) ->
      assert (loans == Set.singleton (name "payload")) "wrong escaping loan reported"
    other -> Left ("return allowed a shared loan to escape: " ++ show other)

testClosedRejectsLinear :: Either String ()
testClosedRejectsLinear = do
  let success = Outcome "success"
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[end]") emptyContext
  case closedFlow success (withContext context) of
    Left (InvalidTerminalState (Closed actual) (UnconsumedLinearResources _)) ->
      assert (actual == success) "closed-path error reported the wrong outcome"
    other -> Left ("closed path accepted a live linear resource: " ++ show other)

testFailedRejectsLinear :: Either String ()
testFailedRejectsLinear = do
  context <- mapLeft show $ insertBinding Linear (name "pending") (nty "PendingRecv") emptyContext
  case failedFlow "recognition" "malformed frame" (withContext context) of
    Left (InvalidTerminalState (Failed cls detail) (UnconsumedLinearResources _)) ->
      assert
        (cls == "recognition" && detail == "malformed frame")
        "failed-path error lost failure classification"
    other -> Left ("failed path accepted a live linear resource: " ++ show other)

testTerminalShortCircuits :: Either String ()
testTerminalShortCircuits = do
  closed <- mapLeft show $ closedFlow (Outcome "failure") emptyCheckState
  failed <- mapLeft show $ failedFlow "transport" "reset" emptyCheckState
  closedResult <- mapLeft show $ sequenceFlow closed (const (Left EmptyBranchSet))
  failedResult <- mapLeft show $ sequenceFlow failed (const (Left EmptyBranchSet))
  closedPath <- solePath closedResult
  failedPath <- solePath failedResult
  assert (pathControl closedPath == Closed (Outcome "failure")) "Closed did not short-circuit"
  assert (pathControl failedPath == Failed "transport" "reset") "Failed did not short-circuit"

testTerminalBranchExcluded :: Either String ()
testTerminalBranchExcluded = do
  context0 <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  (_, terminalContext) <- mapLeft show $ consumeLinear (name "endpoint") context0
  terminal <- mapLeft show $ closedFlow (Outcome "failure") (withContext terminalContext)
  joined <- mapLeft show $ joinBranches [continueFlow (withContext context0), terminal]
  let continuing = pathsWithControl Continue joined
  assert (length continuing == 1) "terminal branch created or removed a continuing path"
  assert
    (Map.member (name "endpoint") (linearBindings (resourceContext (pathState (head continuing)))))
    "terminal branch polluted the continuing branch resource residue"

testContinuingMismatch :: Either String ()
testContinuingMismatch = do
  context0 <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  (_, context1) <- mapLeft show $ consumeLinear (name "endpoint") context0
  case joinBranches [continueFlow (withContext context0), continueFlow (withContext context1)] of
    Left (BranchJoinError (LinearBranchMismatch _ _)) -> Right ()
    other -> Left ("incompatible continuing residues joined: " ++ show other)

testMixedReturnContinue :: Either String ()
testMixedReturnContinue = do
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  returning <- mapLeft show $ returnFlow (nty "Result") (withContext context)
  joined <- mapLeft show $ joinBranches [returning, continueFlow (withContext context)]
  let controls = map pathControl (flowPaths joined)
  assert (Return (nty "Result") `elem` controls) "mixed branch lost its Return path"
  assert (Continue `elem` controls) "mixed branch lost its Continue path"
  assert (length controls == 2) "mixed branch invented an extra path"

testAllTerminal :: Either String ()
testAllTerminal = do
  closed <- mapLeft show $ closedFlow (Outcome "cancelled") emptyCheckState
  failed <- mapLeft show $ failedFlow "storage" "write failed" emptyCheckState
  joined <- mapLeft show $ joinBranches [closed, failed]
  assert
    (all ((/= Continue) . pathControl) (flowPaths joined))
    "all-terminal branch fabricated a continuing result"
  assert (length (flowPaths joined) == 2) "all-terminal branch lost an exit path"

testAffineJoinNormalizes :: Either String ()
testAffineJoinNormalizes = do
  context0 <- mapLeft show $ insertBinding Affine (name "cap") (nty "CancelCap") emptyContext
  (_, context1) <- mapLeft show $ consumeAffine (name "cap") context0
  joined <- mapLeft show $ joinBranches
    [ continueFlow (withContext context0)
    , continueFlow (withContext context1)
    ]
  assert
    (all (Map.null . affineBindings . resourceContext . pathState) (flowPaths joined))
    "continuing branch paths did not normalize to the conservative affine residue"

testPathSensitiveObligations :: Either String ()
testPathSensitiveObligations = do
  let leftObligation = Obligation
        (ObligationId "branch.left")
        (Atom "LeftClaim" [])
        "left"
        "branch-test"
        "branch"
      rightObligation = Obligation
        (ObligationId "branch.right")
        (Atom "RightClaim" [])
        "right"
        "branch-test"
        "branch"
  leftState <- mapLeft show $ emitObligation leftObligation emptyCheckState
  rightState <- mapLeft show $ emitObligation rightObligation emptyCheckState
  joined <- mapLeft show $ joinBranches [continueFlow leftState, continueFlow rightState]
  case flowPaths joined of
    [leftPath, rightPath] -> do
      assert
        (Map.keysSet (residualObligations (pathState leftPath)) == Set.singleton (ObligationId "branch.left"))
        "left branch acquired an obligation from an exclusive branch"
      assert
        (Map.keysSet (residualObligations (pathState rightPath)) == Set.singleton (ObligationId "branch.right"))
        "right branch acquired an obligation from an exclusive branch"
    paths -> Left ("path-sensitive branch join produced unexpected path count: " ++ show (length paths))

withContext :: ResourceContext -> CheckState
withContext context = emptyCheckState { resourceContext = context }

solePath :: ProcessFlow -> Either String FlowPath
solePath flow =
  case flowPaths flow of
    [path] -> Right path
    paths -> Left ("expected one process path, got " ++ show (length paths))

pathsWithControl :: Control -> ProcessFlow -> [FlowPath]
pathsWithControl control = filter ((== control) . pathControl) . flowPaths

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
