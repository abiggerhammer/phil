{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Checker
  ( CheckState (..)
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Process
  ( ProcessFlow
  , continueFlow
  , flowPaths
  , joinBranches
  , pathState
  )
import Phil.Core.Syntax
  ( Obligation (Obligation)
  , ObligationId (ObligationId)
  , Proposition (Atom)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "RES-011 branch obligation survives reconvergence" branchObligationSurvivesJoin
    , test "RES-011 carried obligation survives repeated reconvergence" obligationSurvivesRepeatedJoin
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

branchObligationSurvivesJoin :: Either String ()
branchObligationSurvivesJoin = do
  leftState <- mapLeft show $ emitObligation obligation emptyCheckState
  joined <- mapLeft show $ joinBranches
    [ continueFlow leftState
    , continueFlow emptyCheckState
    ]
  assertObligationPresent joined

obligationSurvivesRepeatedJoin :: Either String ()
obligationSurvivesRepeatedJoin = do
  initialState <- mapLeft show $ emitObligation obligation emptyCheckState
  first <- mapLeft show $ joinBranches
    [ continueFlow initialState
    , continueFlow emptyCheckState
    ]
  carried <- pathContainingObligation first
  second <- mapLeft show $ joinBranches
    [ continueFlow carried
    , continueFlow emptyCheckState
    ]
  assertObligationPresent second

obligation :: Obligation
obligation = Obligation
  (ObligationId "res011.branch.pending")
  (Atom "NeedsDisposition" [])
  "res011"
  "resource-join"
  "before reconvergence"

assertObligationPresent :: ProcessFlow -> Either String ()
assertObligationPresent flow = do
  _ <- pathContainingObligation flow
  Right ()

pathContainingObligation :: ProcessFlow -> Either String CheckState
pathContainingObligation flow =
  case
    [ state
    | path <- flowPaths flow
    , let state = pathState path
    , Map.member (ObligationId "res011.branch.pending") (residualObligations state)
    ] of
    [state] -> Right state
    [] -> Left "unresolved obligation disappeared at reconvergence"
    states -> Left ("unresolved obligation duplicated across paths: " <> show (length states))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
