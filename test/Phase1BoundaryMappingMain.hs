{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping
import Phil.Core.Context (ResourceContext, emptyContext, insertBinding)
import Phil.Core.Recognition
  ( beginRawLoan
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
    [ test "BND-004 exact B/G/T mapping succeeds" exactMappingSucceeds
    , test "BND-004 wrong representation rejects" wrongRepresentationRejects
    , test "BND-004 wrong grammar rejects" wrongGrammarRejects
    , test "BND-004 wrong semantic type rejects" wrongTypeRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactMappingSucceeds :: Either String ()
exactMappingSucceeds = do
  parsed <- recognized
  evidence <- mapLeft show $ mapRecognizedBoundary representation parsed request
  assert (correspondenceRepresentation evidence == repId) "wrong representation in correspondence"
  assert (correspondenceGrammar evidence == grammar) "wrong grammar in correspondence"
  assert (correspondenceValueType evidence == valueType) "wrong type in correspondence"
  assert (correspondenceGrammarValue evidence == grammarValue) "wrong grammar value in correspondence"
  assert (correspondenceSemanticValue evidence == semanticValue) "wrong semantic value in correspondence"

wrongRepresentationRejects :: Either String ()
wrongRepresentationRejects = do
  parsed <- recognized
  case mapRecognizedBoundary representation parsed request { requestedRepresentation = BoundaryRepresentationId "OtherB" } of
    Left (BoundaryRepresentationMismatch _ _) -> Right ()
    other -> Left ("wrong representation did not reject exactly: " <> show other)

wrongGrammarRejects :: Either String ()
wrongGrammarRejects = do
  parsed <- recognized
  case mapRecognizedBoundary representation parsed request { requestedGrammar = GrammarId "OtherG" } of
    Left (BoundaryGrammarMismatch _ _) -> Right ()
    other -> Left ("wrong grammar did not reject exactly: " <> show other)

wrongTypeRejects :: Either String ()
wrongTypeRejects = do
  parsed <- recognized
  case mapRecognizedBoundary representation parsed request { requestedValueType = ValueTypeRevision "OtherT" } of
    Left (BoundaryValueTypeMismatch _ _) -> Right ()
    other -> Left ("wrong value type did not reject exactly: " <> show other)

recognized :: Either String Phil.Core.Recognition.ParsedWitness
recognized = do
  context <- receiveContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context
  mapLeft show $ trustedRecognitionSuccess raw grammarValue borrowed

receiveContext :: Either String ResourceContext
receiveContext = do
  initial <- mapLeft show $ insertBinding Linear endpointName (TyEndpoint session) emptyContext
  step <- mapLeft show $ receiveFrame endpointName pendingName frame initial
  pure (receiveFrameContext step)

representation :: BoundaryRepresentation
representation = BoundaryRepresentation repId grammar valueType

request :: BoundaryMappingRequest
request = BoundaryMappingRequest repId grammar valueType grammarValue semanticValue

repId :: BoundaryRepresentationId
repId = BoundaryRepresentationId "UploadBoundary@rev1"

valueType :: ValueTypeRevision
valueType = ValueTypeRevision "UploadMessage@rev1"

grammar :: GrammarId
grammar = GrammarId "UploadGrammar@rev1"

frame :: FrameId
frame = FrameId "frame-1"

endpointName, pendingName, grammarValue, semanticValue :: Name
endpointName = Name "e0"
pendingName = Name "pending"
grammarValue = Name "g"
semanticValue = Name "t"

session :: Session
session = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
