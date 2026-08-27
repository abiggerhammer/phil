{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.BoundaryMapping
import Phil.Core.BoundaryProgression
import Phil.Core.Context (ResourceContext, emptyContext, insertBinding)
import Phil.Core.QualifiedEncoding
import Phil.Core.Recognition
  ( CommitReceiveStep (..)
  , ParsedWitness
  , beginRawLoan
  , endRawLoan
  , receiveFrame
  , receiveFrameContext
  , trustedRecognitionSuccess
  )
import Phil.Core.Session (SessionStep (..))
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
    [ test "BND-011 receive advances only with exact mapping evidence" mappedReceiveAdvances
    , test "BND-011 mismatched mapping cannot advance receive" mismatchedMappingRejects
    , test "BND-011 partial transport emission cannot advance send" partialSendRejects
    , test "BND-011 complete qualified emission advances send" completeSendAdvances
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

mappedReceiveAdvances :: Either String ()
mappedReceiveAdvances = do
  (parsed, correspondence, context) <- mappedReceiveFixture
  step <- mapLeft show $
    commitMappedReceive pendingName receiveSuccessor parsed correspondence context
  assert (fst (commitSuccessor step) == receiveSuccessor) "receive successor changed"

mismatchedMappingRejects :: Either String ()
mismatchedMappingRejects = do
  (parsed, correspondence, context) <- mappedReceiveFixture
  let wrong = correspondence { correspondenceGrammarValue = Name "other-g" }
  case commitMappedReceive pendingName receiveSuccessor parsed wrong context of
    Left ReceiveMappingValueMismatch -> Right ()
    other -> Left ("mismatched mapping did not reject before progression: " <> show other)

partialSendRejects :: Either String ()
partialSendRejects = do
  generated <- qualifiedGenerated
  case establishCompleteEmission generated (EmissionExtent 6 5) of
    Left (PartialTransportEmission _) -> Right ()
    other -> Left ("partial emission was accepted: " <> show other)

completeSendAdvances :: Either String ()
completeSendAdvances = do
  generated <- qualifiedGenerated
  emission <- mapLeft show $ establishCompleteEmission generated (EmissionExtent 6 6)
  context <- sendContext
  step <- mapLeft show $
    commitQualifiedSend sendEndpointName sendSuccessor generated emission context
  assert (fmap fst (stepSuccessor step) == Just sendSuccessor) "send successor changed"

mappedReceiveFixture :: Either String (ParsedWitness, CorrespondenceEvidence, ResourceContext)
mappedReceiveFixture = do
  initial <- mapLeft show $ insertBinding Linear receiveEndpointName (TyEndpoint receiveSession) emptyContext
  framed <- mapLeft show $ receiveFrame receiveEndpointName pendingName frame initial
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName (receiveFrameContext framed)
  parsed <- mapLeft show $ trustedRecognitionSuccess raw grammarValue borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  correspondence <- mapLeft show $ mapRecognizedBoundary representation parsed mappingRequest
  pure (parsed, correspondence, ended)

qualifiedGenerated :: Either String GeneratedEncodingEvidence
qualifiedGenerated = mapLeft show $
  establishGeneratedEncoding encoder repId outputOwner outputOwner

sendContext :: Either String ResourceContext
sendContext = mapLeft show $
  insertBinding Linear sendEndpointName (TyEndpoint sendSession) emptyContext

representation :: BoundaryRepresentation
representation = BoundaryRepresentation repId grammar valueType

mappingRequest :: BoundaryMappingRequest
mappingRequest = BoundaryMappingRequest repId grammar valueType grammarValue semanticValue

encoder :: QualifiedEncoder
encoder = QualifiedEncoder
  { encoderImplementation = Name "encoder@rev1"
  , encoderRepresentation = repId
  , encoderAdmission = EncodingAdmitted
  }

repId :: BoundaryRepresentationId
repId = BoundaryRepresentationId "UploadBoundary@rev1"

valueType :: ValueTypeRevision
valueType = ValueTypeRevision "UploadMessage@rev1"

grammar :: GrammarId
grammar = GrammarId "UploadGrammar@rev1"

frame :: FrameId
frame = FrameId "frame-1"

receiveEndpointName, pendingName, receiveSuccessor :: Name
receiveEndpointName = Name "recv-e0"
pendingName = Name "pending"
receiveSuccessor = Name "recv-e1"

grammarValue, semanticValue :: Name
grammarValue = Name "g"
semanticValue = Name "t"

sendEndpointName, sendSuccessor, outputOwner :: Name
sendEndpointName = Name "send-e0"
sendSuccessor = Name "send-e1"
outputOwner = Name "encoded-frame"

receiveSession :: Session
receiveSession = Receive (Name "message") (TyFrame grammar) (End (Outcome "done"))

sendSession :: Session
sendSession = Send (Name "message") (TyFrame grammar) (End (Outcome "done"))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
