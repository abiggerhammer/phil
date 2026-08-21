{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , completeComponent
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Process
  ( flowPaths
  , closedFlow
  , failedFlow
  , pathControl
  , pathState
  )
import Phil.Core.Recognition
  ( CommitReceiveStep (..)
  , ReceiveFrameStep (..)
  , beginRawLoan
  , commitReceive
  , endRawLoan
  , failPendingRecognition
  , receiveFrame
  , recognitionFailureDetail
  , trustedRecognitionFailure
  , trustedRecognitionSuccess
  )
import Phil.Core.Session (SessionStep (..), closeEndpoint)
import Phil.Core.Syntax
  ( Control (..)
  , FrameId (FrameId)
  , GrammarId (GrammarId)
  , Mode (Linear)
  , Name (Name)
  , Outcome (Outcome)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "unresolved PendingRecv cannot complete a component" testPendingMustBeResolved
    , test "recognized frame commits into session close and Closed control" testRecognitionSuccessLifecycle
    , test "recognition failure discharges pending into Failed control" testRecognitionFailureLifecycle
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

grammar :: GrammarId
grammar = GrammarId "Hello"

frameId :: FrameId
frameId = FrameId "hello-1"

success :: Outcome
success = Outcome "success"

session :: Session
session = Receive (name "hello") (TyFrame grammar) (End success)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " ++ label) >> pure True
  Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testPendingMustBeResolved :: Either String ()
testPendingMustBeResolved = do
  step <- receivePending
  let state = emptyCheckState { resourceContext = receiveFrameContext step }
  case completeComponent state of
    Left (ResourceError (UnconsumedLinearResources leftovers)) ->
      assert (Map.member (name "pending") leftovers) "PendingRecv missing from linear residue"
    other -> Left ("component completed with unresolved PendingRecv: " ++ show other)

testRecognitionSuccessLifecycle :: Either String ()
testRecognitionSuccessLifecycle = do
  step <- receivePending
  (raw, borrowed) <- mapLeft show $ beginRawLoan (name "pending") (receiveFrameContext step)
  parsed <- mapLeft show $ trustedRecognitionSuccess raw (name "hello-value") borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  committed <- mapLeft show $ commitReceive (name "pending") (name "e1") parsed ended
  assert (commitParsedWitness committed == parsed) "commit_receive consumed parsed proof ownership"
  closedStep <- mapLeft show $ closeEndpoint (name "e1") success (commitContext committed)
  flow <- mapLeft show $ closedFlow success (emptyCheckState { resourceContext = stepContext closedStep })
  case flowPaths flow of
    [path] -> do
      assert (pathControl path == Closed success) "wrong process control after declared close"
      assert (Map.null (linearBindings (resourceContext (pathState path)))) "closed path retained linear residue"
    other -> Left ("declared close produced unexpected process paths: " ++ show other)

testRecognitionFailureLifecycle :: Either String ()
testRecognitionFailureLifecycle = do
  step <- receivePending
  (raw, borrowed) <- mapLeft show $ beginRawLoan (name "pending") (receiveFrameContext step)
  failure <- mapLeft show $ trustedRecognitionFailure raw "invalid tag" borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  terminated <- mapLeft show $ failPendingRecognition (name "pending") failure ended
  flow <- mapLeft show $ failedFlow "recognition" (recognitionFailureDetail failure)
    (emptyCheckState { resourceContext = terminated })
  case flowPaths flow of
    [path] -> do
      assert (pathControl path == Failed "recognition" "invalid tag") "wrong fatal process control"
      assert (Map.null (linearBindings (resourceContext (pathState path)))) "failed path retained pending resource"
    other -> Left ("recognition failure produced unexpected process paths: " ++ show other)

receivePending :: Either String ReceiveFrameStep
receivePending = do
  context <- mapLeft show $ insertBinding Linear (name "e0") (TyEndpoint session) emptyContext
  mapLeft show $ receiveFrame (name "e0") (name "pending") frameId context

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
