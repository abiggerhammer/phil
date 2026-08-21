{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Recognition
  ( RecognitionError (..)
  , ReceiveFrameStep (..)
  , beginRawLoan
  , commitReceive
  , endRawLoan
  , failPendingRecognition
  , receiveFrame
  , trustedRecognitionFailure
  , trustedRecognitionSuccess
  )
import Phil.Core.Session
  ( SessionError (..)
  , offerEndpoint
  , receiveEndpoint
  )
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (FrameId)
  , GrammarId (GrammarId)
  , Mode (Linear)
  , Name (Name)
  , Outcome (Outcome)
  , PendingRecvSpec (..)
  , Proposition (Truth)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "generic receive rejects grammar-backed messages" testGenericReceiveRejectsFrame
    , test "generic receive rejects refined grammar-backed messages" testGenericReceiveRejectsRefinedFrame
    , test "external-choice frame payloads fail closed" testOfferFramePayloadFailsClosed
    , test "receive_frame consumes endpoint and creates only PendingRecv" testReceiveFrameCreatesPending
    , test "receive_frame rejects ordinary receives" testReceiveFrameRejectsOrdinaryReceive
    , test "pending receive must use a fresh identity" testPendingFreshIdentity
    , test "raw loan blocks commit_receive" testRawLoanBlocksCommit
    , test "raw loan blocks pending destruction" testRawLoanBlocksFailure
    , test "stale raw view cannot construct recognition evidence" testStaleRawViewRejected
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
frameSession grammarId = Receive (name "value") (TyFrame grammarId) (End success)

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testGenericReceiveRejectsFrame :: Either String ()
testGenericReceiveRejectsFrame = do
  let g = grammar "Hello"
  context <- endpointContext (name "e0") (frameSession g)
  case receiveEndpoint (name "e0") (name "e1") context of
    Left (GrammarBackedReceiveRequiresRecognition actual) ->
      assert (actual == g) "wrong grammar reported"
    other -> Left ("grammar-backed receive bypassed recognition: " ++ show other)

testGenericReceiveRejectsRefinedFrame :: Either String ()
testGenericReceiveRejectsRefinedFrame = do
  let g = grammar "Hello"
      messageTy = TyRefined (name "hello") (TyFrame g) Truth
      session = Receive (name "hello") messageTy (End success)
  context <- endpointContext (name "e0") session
  case receiveEndpoint (name "e0") (name "e1") context of
    Left (GrammarBackedReceiveRequiresRecognition actual) ->
      assert (actual == g) "wrong refined-frame grammar reported"
    other -> Left ("refined grammar-backed receive bypassed recognition: " ++ show other)

testOfferFramePayloadFailsClosed :: Either String ()
testOfferFramePayloadFailsClosed = do
  let g = grammar "ChoiceFrame"
      session = Offer [Branch "frame" (Just (name "msg", TyFrame g)) (End success)]
  context <- endpointContext (name "e0") session
  case offerEndpoint (name "e0") (name "e1") "frame" context of
    Left (GrammarBackedOfferPayloadRequiresRecognition label actual) ->
      assert (label == "frame" && actual == g) "wrong offer diagnostic"
    other -> Left ("grammar-backed external-choice payload advanced unsafely: " ++ show other)

testReceiveFrameCreatesPending :: Either String ()
testReceiveFrameCreatesPending = do
  let g = grammar "Hello"
      f = frame "hello-1"
  context <- endpointContext (name "e0") (frameSession g)
  step <- mapLeft show $ receiveFrame (name "e0") (name "pending") f context
  let pending = receivePendingSpec step
      linear = linearBindings (receiveFrameContext step)
  assert (Map.notMember (name "e0") linear) "source endpoint survived receive_frame"
  assert (Map.lookup (name "pending") linear == Just (TyPendingRecv pending)) "pending owner missing"
  assert (pendingGrammar pending == g && pendingFrame pending == f) "pending lost provenance"
  assert (not (any isEndpoint (Map.elems linear))) "successor exists before recognition"

testReceiveFrameRejectsOrdinaryReceive :: Either String ()
testReceiveFrameRejectsOrdinaryReceive = do
  let session = Receive (name "v") (TyUInt 16) (End success)
  context <- endpointContext (name "e0") session
  case receiveFrame (name "e0") (name "pending") (frame "ordinary") context of
    Left (ExpectedGrammarBackedReceive endpoint messageTy) ->
      assert (endpoint == name "e0" && messageTy == TyUInt 16) "wrong diagnostic"
    other -> Left ("receive_frame accepted non-grammar receive: " ++ show other)

testPendingFreshIdentity :: Either String ()
testPendingFreshIdentity = do
  context <- endpointContext (name "e0") (frameSession (grammar "Hello"))
  case receiveFrame (name "e0") (name "e0") (frame "hello") context of
    Left (PendingReusesSourceEndpoint endpoint) -> assert (endpoint == name "e0") "wrong identity"
    other -> Left ("receive_frame reused consumed endpoint identity: " ++ show other)

testRawLoanBlocksCommit :: Either String ()
testRawLoanBlocksCommit = do
  (pendingName, context0) <- pendingContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  parsed <- mapLeft show $ trustedRecognitionSuccess raw (name "hello") borrowed
  case commitReceive pendingName (name "e1") parsed borrowed of
    Left (RecognitionResourceError (OwnerBorrowed owner)) -> assert (owner == pendingName) "wrong owner"
    other -> Left ("commit_receive consumed borrowed pending: " ++ show other)

testRawLoanBlocksFailure :: Either String ()
testRawLoanBlocksFailure = do
  (pendingName, context0) <- pendingContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  failure <- mapLeft show $ trustedRecognitionFailure raw "bad frame" borrowed
  case failPendingRecognition pendingName failure borrowed of
    Left (RecognitionResourceError (OwnerBorrowed owner)) -> assert (owner == pendingName) "wrong owner"
    other -> Left ("pending was consumed while raw loan was live: " ++ show other)

testStaleRawViewRejected :: Either String ()
testStaleRawViewRejected = do
  (pendingName, context0) <- pendingContext
  (raw, borrowed) <- mapLeft show $ beginRawLoan pendingName context0
  ended <- mapLeft show $ endRawLoan raw borrowed
  case trustedRecognitionSuccess raw (name "hello") ended of
    Left (RawLoanNotActive owner) -> assert (owner == pendingName) "wrong stale raw owner"
    other -> Left ("stale raw view created parsed evidence: " ++ show other)

pendingContext :: Either String (Name, ResourceContext)
pendingContext = do
  context <- endpointContext (name "e0") (frameSession (grammar "Hello"))
  step <- mapLeft show $ receiveFrame (name "e0") (name "pending") (frame "hello") context
  pure (name "pending", receiveFrameContext step)

endpointContext :: Name -> Session -> Either String ResourceContext
endpointContext endpoint session = mapLeft show $ insertBinding Linear endpoint (TyEndpoint session) emptyContext

isEndpoint :: Ty -> Bool
isEndpoint (TyEndpoint _) = True
isEndpoint _ = False

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
