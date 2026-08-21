{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Context
  ( ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Recognition
  ( CommitReceiveStep (..)
  , ParsedWitness
  , RecognitionError (..)
  , RecognitionFailure
  , ReceiveFrameStep (..)
  , beginRawLoan
  , commitReceive
  , endRawLoan
  , failPendingRecognition
  , parsedFrameId
  , parsedGrammarId
  , parsedPendingOwner
  , parsedValueName
  , receiveFrame
  , recognitionFailureDetail
  , trustedRecognitionFailure
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
    [ test "commit_receive requires matching pending provenance" testPendingProvenance
    , test "commit_receive requires matching grammar identity" testGrammarIdentity
    , test "commit_receive requires matching frame identity" testFrameIdentity
    , test "commit_receive consumes pending and creates declared successor" testCommitProgression
    , test "commit_receive cannot reuse ingress identities" testCommitFreshIdentity
    , test "recognition failure consumes pending after loan ends" testFailureConsumesPending
    , test "pending destruction requires matching failure provenance" testFailureProvenance
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

grammar :: Text -> GrammarId
grammar = GrammarId

frame :: Text -> FrameId
frame = FrameId

success :: Outcome
success = Outcome "success"

frameSession :: GrammarId -> Session
frameSession g = Receive (name "value") (TyFrame g) (End success)

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " ++ label) >> pure True
  Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testPendingProvenance :: Either String ()
testPendingProvenance = do
  witness <- makeWitness (name "other-e") (name "other-p") (grammar "Hello") (frame "same-frame")
  (pendingName, context) <- pendingContext (name "e0") (name "pending") (grammar "Hello") (frame "same-frame")
  case commitReceive pendingName (name "e1") witness context of
    Left (ParsedEvidenceMismatch _ _) -> Right ()
    other -> Left ("unrelated pending evidence committed: " ++ show other)

testGrammarIdentity :: Either String ()
testGrammarIdentity = do
  witness <- makeWitness (name "w-e") (name "pending") (grammar "Begin") (frame "frame-1")
  (pendingName, context) <- pendingContext (name "e0") (name "pending") (grammar "Hello") (frame "frame-1")
  case commitReceive pendingName (name "e1") witness context of
    Left (ParsedEvidenceMismatch _ _) -> Right ()
    other -> Left ("evidence for another grammar committed: " ++ show other)

testFrameIdentity :: Either String ()
testFrameIdentity = do
  witness <- makeWitness (name "w-e") (name "pending") (grammar "Hello") (frame "frame-2")
  (pendingName, context) <- pendingContext (name "e0") (name "pending") (grammar "Hello") (frame "frame-1")
  case commitReceive pendingName (name "e1") witness context of
    Left (ParsedEvidenceMismatch _ _) -> Right ()
    other -> Left ("evidence for another frame committed: " ++ show other)

testCommitProgression :: Either String ()
testCommitProgression = do
  let g = grammar "Hello"
      f = frame "hello"
      pendingName = name "pending"
  (_, context0) <- pendingContext (name "e0") pendingName g f
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  parsed <- mapLeft show $ trustedRecognitionSuccess raw (name "hello-value") borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  committed <- mapLeft show $ commitReceive pendingName (name "e1") parsed ended
  let linear = linearBindings (commitContext committed)
  assert (Map.notMember pendingName linear) "pending survived commit_receive"
  assert (Map.lookup (name "e1") linear == Just (TyEndpoint (End success))) "wrong successor"
  assert
    ( parsedPendingOwner parsed == pendingName
      && parsedGrammarId parsed == g
      && parsedFrameId parsed == f
      && parsedValueName parsed == name "hello-value"
    )
    "parsed witness lost provenance"

testCommitFreshIdentity :: Either String ()
testCommitFreshIdentity = do
  let pendingName = name "pending"
  (_, context0) <- pendingContext (name "e0") pendingName (grammar "Hello") (frame "hello")
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  parsed <- mapLeft show $ trustedRecognitionSuccess raw (name "hello") borrowed
  ended <- mapLeft show $ endRawLoan raw borrowed
  case commitReceive pendingName (name "e0") parsed ended of
    Left (SuccessorReusesIngressIdentity reused) -> assert (reused == name "e0") "wrong source identity"
    other -> Left ("source endpoint identity reused: " ++ show other)
  case commitReceive pendingName pendingName parsed ended of
    Left (SuccessorReusesIngressIdentity reused) -> assert (reused == pendingName) "wrong pending identity"
    other -> Left ("pending identity reused: " ++ show other)

testFailureConsumesPending :: Either String ()
testFailureConsumesPending = do
  let pendingName = name "pending"
  (_, context0) <- pendingContext (name "e0") pendingName (grammar "Hello") (frame "hello")
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  failure <- mapLeft show $ trustedRecognitionFailure raw "invalid tag" borrowed
  assert (recognitionFailureDetail failure == "invalid tag") "failure detail lost"
  ended <- mapLeft show $ endRawLoan raw borrowed
  terminated <- mapLeft show $ failPendingRecognition pendingName failure ended
  assert (Map.null (linearBindings terminated)) "fatal recognition fabricated successor"

testFailureProvenance :: Either String ()
testFailureProvenance = do
  failure <- makeFailure (name "other-e") (name "other-p") (grammar "Hello") (frame "same-frame")
  (pendingName, context) <- pendingContext (name "e0") (name "pending") (grammar "Hello") (frame "same-frame")
  case failPendingRecognition pendingName failure context of
    Left (RecognitionFailureMismatch _ _) -> Right ()
    other -> Left ("unrelated recognition failure destroyed pending: " ++ show other)

pendingContext :: Name -> Name -> GrammarId -> FrameId -> Either String (Name, ResourceContext)
pendingContext endpoint pendingName g f = do
  context <- endpointContext endpoint (frameSession g)
  step <- mapLeft show $ receiveFrame endpoint pendingName f context
  pure (pendingName, receiveFrameContext step)

makeWitness :: Name -> Name -> GrammarId -> FrameId -> Either String ParsedWitness
makeWitness endpoint pendingName g f = do
  (_, context0) <- pendingContext endpoint pendingName g f
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  witness <- mapLeft show $ trustedRecognitionSuccess raw (name "value") borrowed
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure witness

makeFailure :: Name -> Name -> GrammarId -> FrameId -> Either String RecognitionFailure
makeFailure endpoint pendingName g f = do
  (_, context0) <- pendingContext endpoint pendingName g f
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  failure <- mapLeft show $ trustedRecognitionFailure raw "failure" borrowed
  _ <- mapLeft show $ endRawLoan raw borrowed
  pure failure

endpointContext :: Name -> Session -> Either String ResourceContext
endpointContext endpoint session = mapLeft show $ insertBinding Linear endpoint (TyEndpoint session) emptyContext

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
