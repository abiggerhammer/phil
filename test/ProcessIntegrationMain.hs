{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Checker
  ( CheckState (..)
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Process
  ( ProcessFlow
  , closedFlow
  , continueFlow
  , flowPaths
  , pathControl
  , pathState
  , sequenceFlow
  )
import Phil.Core.Session
  ( SessionStep (..)
  , closeEndpoint
  )
import Phil.Core.Syntax
  ( Control (..)
  , Mode (Linear)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , Proposition (Atom)
  , Session (End)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "sequential composition accumulates residual obligations" testSequentialObligationUnion
    , test "declared session close composes into Closed process control" testSessionCloseComposition
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testSequentialObligationUnion :: Either String ()
testSequentialObligationUnion = do
  let first = Obligation
        (ObligationId "sequence.first")
        (Atom "FirstClaim" [])
        "first"
        "sequence"
      second = Obligation
        (ObligationId "sequence.second")
        (Atom "SecondClaim" [])
        "second"
        "sequence"
  state1 <- mapLeft show $ emitObligation first emptyCheckState
  flow <- mapLeft show $ sequenceFlow (continueFlow state1) $ \state -> do
    state2 <- emitObligation second state
    pure (continueFlow state2)
  state <- soleState flow
  assert
    (Map.keysSet (residualObligations state)
      == Set.fromList [ObligationId "sequence.first", ObligationId "sequence.second"])
    "sequential composition did not preserve Φ1 ∪ Φ2"

testSessionCloseComposition :: Either String ()
testSessionCloseComposition = do
  let success = Outcome "success"
      endpoint = Name "e0"
  context <- endpointContext endpoint (End success)
  step <- mapLeft show $ closeEndpoint endpoint success context
  flow <- mapLeft show $ closedFlow success
    (emptyCheckState { resourceContext = stepContext step })
  case flowPaths flow of
    [path] -> do
      assert (pathControl path == Closed success) "session close did not become Closed control"
      assert
        (Map.null (linearBindings (resourceContext (pathState path))))
        "Closed process path retained a linear endpoint after declared close"
    paths -> Left ("expected one Closed path, got " ++ show (length paths))

endpointContext :: Name -> Session -> Either String ResourceContext
endpointContext endpoint session =
  mapLeft show $ insertBinding Linear endpoint (TyEndpoint session) emptyContext

soleState :: ProcessFlow -> Either String CheckState
soleState flow =
  case flowPaths flow of
    [path] -> Right (pathState path)
    paths -> Left ("expected one process path, got " ++ show (length paths))

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
