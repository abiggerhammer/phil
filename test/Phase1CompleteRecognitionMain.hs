{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

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
  , rawFrameId
  , rawGrammarId
  , rawPendingOwner
  , receiveFrame
  , receiveFrameContext
  , trustedRecognitionSuccess
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
    [ test "BND-001 exact complete frame keeps raw provenance" exactRawProvenance
    , test "BND-001 recognition constructs exact Parsed witness" exactParsedProvenance
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactRawProvenance :: Either String ()
exactRawProvenance = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  assert (rawPendingOwner raw == pendingName) "raw view lost exact pending owner"
  assert (rawGrammarId raw == grammar) "raw view lost exact grammar"
  assert (rawFrameId raw == frame) "raw view lost exact frame"
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure ()

exactParsedProvenance :: Either String ()
exactParsedProvenance = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  parsed <- mapLeft show $ trustedRecognitionSuccess raw valueName borrowed
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
frame = FrameId "transport-frame-42"

session :: Session
session = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
