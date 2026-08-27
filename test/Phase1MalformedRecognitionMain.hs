{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.BoundaryRecognition
  ( RecognitionExtent (..)
  , rejectMalformedCompleteFrame
  )
import Phil.Core.Context
  ( ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Recognition
  ( beginRawLoan
  , endRawLoan
  , failPendingRecognition
  , recognitionFailureDetail
  , recognitionFailureFrame
  , recognitionFailureGrammar
  , recognitionPendingOwner
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
    [ test "BND-003 malformed complete frame yields only recognition failure" malformedYieldsFailure
    , test "BND-003 recognition failure creates no success successor endpoint" malformedCreatesNoSuccessor
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

malformedYieldsFailure :: Either String ()
malformedYieldsFailure = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  failure <- mapLeft show $
    rejectMalformedCompleteFrame raw "invalid tag" exactExtent borrowed
  assert (recognitionPendingOwner failure == pendingName) "failure names wrong pending owner"
  assert (recognitionFailureGrammar failure == grammar) "failure names wrong grammar"
  assert (recognitionFailureFrame failure == frame) "failure names wrong complete frame"
  assert (recognitionFailureDetail failure == "invalid tag") "failure detail changed"
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure ()

malformedCreatesNoSuccessor :: Either String ()
malformedCreatesNoSuccessor = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  failure <- mapLeft show $
    rejectMalformedCompleteFrame raw "invalid tag" exactExtent borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  terminated <- mapLeft show $ failPendingRecognition pendingName failure ended
  assert (Map.null (linearBindings terminated))
    "recognition failure left a pending receive or success successor endpoint"

receiveContext :: Either String ResourceContext
receiveContext = do
  initial <- mapLeft show $ insertBinding Linear endpointName (TyEndpoint session) emptyContext
  step <- mapLeft show $ receiveFrame endpointName pendingName frame initial
  pure (receiveFrameContext step)

endpointName, pendingName :: Name
endpointName = Name "e0"
pendingName = Name "pending-frame"

grammar :: GrammarId
grammar = GrammarId "HelloGrammar@rev1"

frame :: FrameId
frame = FrameId "transport-frame-malformed"

session :: Session
session = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

exactExtent :: RecognitionExtent
exactExtent = RecognitionExtent
  { declaredFrameBytes = 6
  , consumedFrameBytes = 6
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
