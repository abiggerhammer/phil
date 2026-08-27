{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryRecognition
  ( CompleteRecognitionError (..)
  , RecognitionExtent (..)
  , recognizeCompleteFrame
  )
import Phil.Core.Context
  ( ResourceContext
  , emptyContext
  , insertBinding
  )
import Phil.Core.Recognition
  ( beginRawLoan
  , endRawLoan
  , parsedFrameId
  , parsedGrammarId
  , parsedPendingOwner
  , parsedValueName
  , receiveFrame
  , receiveFrameContext
  )
import Phil.Core.Syntax
  ( FrameId (FrameId)
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
    [ test "BND-002 valid prefix with in-frame suffix is rejected" trailingSuffixRejected
    , test "BND-002 exact complete consumption still recognizes" exactConsumptionAccepted
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

trailingSuffixRejected :: Either String ()
trailingSuffixRejected = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  let extent = RecognitionExtent
        { declaredFrameBytes = 6
        , consumedFrameBytes = 5
        }
  case recognizeCompleteFrame raw valueName extent borrowed of
    Left (TrailingBytesInsideFrame actual) ->
      assert (actual == extent) "rejection reported the wrong recognition extent"
    other -> Left ("valid prefix with trailing byte was accepted: " <> show other)
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure ()

exactConsumptionAccepted :: Either String ()
exactConsumptionAccepted = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  parsed <- mapLeft show $ recognizeCompleteFrame raw valueName
    RecognitionExtent
      { declaredFrameBytes = 5
      , consumedFrameBytes = 5
      }
    borrowed
  assert (parsedPendingOwner parsed == pendingName) "Parsed witness names wrong raw owner"
  assert (parsedGrammarId parsed == grammar) "Parsed witness names wrong grammar"
  assert (parsedFrameId parsed == frame) "Parsed witness names wrong complete frame"
  assert (parsedValueName parsed == valueName) "Parsed witness names wrong grammar value"
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure ()

receiveContext :: Either String ResourceContext
receiveContext = do
  initial <- mapLeft show $ insertBinding Linear endpointName (TyEndpoint session) emptyContext
  step <- mapLeft show $ receiveFrame endpointName pendingName frame initial
  pure (receiveFrameContext step)

endpointName, pendingName, valueName :: Name
endpointName = Name "e0"
pendingName = Name "pending-frame"
valueName = Name "hello-value"

grammar :: GrammarId
grammar = GrammarId "HelloGrammar@rev1"

frame :: FrameId
frame = FrameId "transport-frame-43"

session :: Session
session = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
