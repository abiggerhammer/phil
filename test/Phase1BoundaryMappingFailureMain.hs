{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping
import Phil.Core.Context (ResourceContext, emptyContext, insertBinding)
import Phil.Core.Recognition
  ( ParsedWitness
  , beginRawLoan
  , parsedGrammarId
  , parsedValueName
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
    [ test "BND-005 valid grammar value can fail mapping distinctly" validRecognitionFailsMapping
    , test "BND-005 mapping rejection does not erase Parsed provenance" parsedProvenanceSurvivesMappingFailure
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

validRecognitionFailsMapping :: Either String ()
validRecognitionFailsMapping = do
  parsed <- recognized
  case mapRecognizedBoundaryWithDisposition representation parsed request
      (MappingRejected "semantic value outside partial correspondence") of
    Left (BoundaryMappingFailure actualRep actualGrammarValue detail) -> do
      assert (actualRep == repId) "mapping failure named wrong representation"
      assert (actualGrammarValue == grammarValue) "mapping failure named wrong grammar value"
      assert (detail == "semantic value outside partial correspondence") "mapping failure lost detail"
    other -> Left ("partial boundary rejection was misclassified: " <> show other)

parsedProvenanceSurvivesMappingFailure :: Either String ()
parsedProvenanceSurvivesMappingFailure = do
  parsed <- recognized
  case mapRecognizedBoundaryWithDisposition representation parsed request (MappingRejected "no mapping") of
    Left (BoundaryMappingFailure _ _ _) -> do
      assert (parsedGrammarId parsed == grammar) "recognition provenance lost grammar after mapping failure"
      assert (parsedValueName parsed == grammarValue) "recognition provenance lost grammar value after mapping failure"
    other -> Left ("expected boundary-mapping failure, got: " <> show other)

recognized :: Either String ParsedWitness
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
