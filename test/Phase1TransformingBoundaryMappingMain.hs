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
    [ test "BND-006 transforming mapping creates distinct semantic value" transformingMappingIsDistinct
    , test "BND-006 transformation preserves recognized subject" transformationPreservesParsedSubject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

transformingMappingIsDistinct :: Either String ()
transformingMappingIsDistinct = do
  parsed <- recognized
  evidence <- mapLeft show $ mapRecognizedBoundary representation parsed request
  assert (correspondenceGrammarValue evidence == grammarValue) "correspondence lost recognized grammar value"
  assert (correspondenceSemanticValue evidence == normalizedValue) "correspondence lost transformed semantic value"
  assert (correspondenceGrammarValue evidence /= correspondenceSemanticValue evidence) "transforming mapping collapsed source and target identity"

transformationPreservesParsedSubject :: Either String ()
transformationPreservesParsedSubject = do
  parsed <- recognized
  _ <- mapLeft show $ mapRecognizedBoundary representation parsed request
  assert (parsedGrammarId parsed == grammar) "mapping rewrote Parsed grammar"
  assert (parsedValueName parsed == grammarValue) "mapping retargeted Parsed to transformed semantic value"

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
request = BoundaryMappingRequest repId grammar valueType grammarValue normalizedValue

repId :: BoundaryRepresentationId
repId = BoundaryRepresentationId "UploadBoundary@rev1"

valueType :: ValueTypeRevision
valueType = ValueTypeRevision "NormalizedUpload@rev1"

grammar :: GrammarId
grammar = GrammarId "UploadGrammar@rev1"

frame :: FrameId
frame = FrameId "frame-1"

endpointName, pendingName, grammarValue, normalizedValue :: Name
endpointName = Name "e0"
pendingName = Name "pending"
grammarValue = Name "wire-record"
normalizedValue = Name "normalized-domain-record"

session :: Session
session = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
