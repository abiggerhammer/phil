{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError (..)
  , completeComponent
  , emitObligation
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeAffine
  , consumeLinear
  , emptyContext
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  , useUnrestricted
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionAction (..)
  , SessionError (..)
  , SessionStep (..)
  , closeEndpoint
  , dualSession
  , exposeSessionHead
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Mode (..)
  , Name (Name)
  , Obligation (Obligation)
  , ObligationId (ObligationId)
  , Outcome (Outcome)
  , Proposition (Atom)
  , Session (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Γ values are reusable" testUnrestrictedReuse
    , test "A values are consumable at most once" testAffineAtMostOnce
    , test "shared loan blocks owner consumption" testSharedLoanBlocksConsumption
    , test "Δ mismatch rejects branch join" testLinearBranchMismatch
    , test "A join conservatively forgets consumed capability" testAffineJoinForgets
    , test "complete component rejects leftover Δ" testLinearResidueRejected
    , test "obligation IDs reject conflicting reuse" testObligationIdConflict
    , test "send consumes old endpoint and creates declared successor" testSendProgression
    , test "wrong session polarity is rejected" testWrongPolarity
    , test "select exposes branch payload and continuation" testSelectProgression
    , test "unknown session labels are rejected" testUnknownLabel
    , test "offer cannot be used on internal choice" testOfferWrongPolarity
    , test "close consumes endpoint only at matching outcome" testCloseProgression
    , test "guarded recursion exposes one communication head" testGuardedRecursion
    , test "unguarded recursion is rejected" testUnguardedRecursion
    , test "session duality is involutive" testDuality
    ]
  unless (and results) exitFailure

name :: Text -> Name
name = Name

nty :: Text -> Ty
nty = TyOpaque

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testUnrestrictedReuse :: Either String ()
testUnrestrictedReuse = do
  context0 <- mapLeft show $ insertBinding Unrestricted (name "policy") (nty "Policy") emptyContext
  (_, context1) <- mapLeft show $ useUnrestricted (name "policy") context0
  (_, context2) <- mapLeft show $ useUnrestricted (name "policy") context1
  assert (context2 == context0) "unrestricted use changed Γ"

testAffineAtMostOnce :: Either String ()
testAffineAtMostOnce = do
  context0 <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, context1) <- mapLeft show $ consumeAffine (name "cap") context0
  case consumeAffine (name "cap") context1 of
    Left (UnknownBinding _) -> Right ()
    other -> Left ("second affine consumption was not rejected as expected: " ++ show other)

testSharedLoanBlocksConsumption :: Either String ()
testSharedLoanBlocksConsumption = do
  context0 <- mapLeft show $ insertBinding Linear (name "payload") (nty "Bytes[4096]") emptyContext
  context1 <- mapLeft show $ startSharedLoan (name "payload") context0
  case consumeLinear (name "payload") context1 of
    Left (OwnerBorrowed _) -> pure ()
    other -> Left ("borrowed owner consumption was not rejected: " ++ show other)
  context2 <- mapLeft show $ endSharedLoan (name "payload") context1
  (_, context3) <- mapLeft show $ consumeLinear (name "payload") context2
  mapLeft show $ ensureComplete context3

testLinearBranchMismatch :: Either String ()
testLinearBranchMismatch = do
  incoming <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  (_, consumed) <- mapLeft show $ consumeLinear (name "endpoint") incoming
  case joinContinuing [incoming, consumed] of
    Left (LinearBranchMismatch _ _) -> Right ()
    other -> Left ("linear branch mismatch was not rejected: " ++ show other)

testAffineJoinForgets :: Either String ()
testAffineJoinForgets = do
  incoming <- mapLeft show $ insertBinding Affine (name "cap") (nty "Capability") emptyContext
  (_, consumed) <- mapLeft show $ consumeAffine (name "cap") incoming
  joined <- mapLeft show $ joinContinuing [incoming, consumed]
  assert (Map.null (affineBindings joined)) "affine capability survived a join where one branch consumed it"

testLinearResidueRejected :: Either String ()
testLinearResidueRejected = do
  context <- mapLeft show $ insertBinding Linear (name "endpoint") (nty "Endpoint[S]") emptyContext
  let state = emptyCheckState { resourceContext = context }
  case completeComponent state of
    Left (ResourceError (UnconsumedLinearResources _)) -> Right ()
    other -> Left ("leftover linear resource was not rejected: " ++ show other)

testObligationIdConflict :: Either String ()
testObligationIdConflict = do
  let first = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" ["κ1", "begin"])
        "server.phil:begin"
        "before Accept"
      conflicting = Obligation
        (ObligationId "upload.begin.policy")
        (Atom "BeginPolicy" ["κ2", "begin"])
        "server.phil:begin"
        "before Accept"
  state1 <- mapLeft show $ emitObligation first emptyCheckState
  _ <- mapLeft show $ emitObligation first state1
  case emitObligation conflicting state1 of
    Left (ConflictingObligationId _ _) -> Right ()
    other -> Left ("conflicting obligation identity was not rejected: " ++ show other)

testSendProgression :: Either String ()
testSendProgression = do
  let success = Outcome "success"
      session = Send (name "payload") (nty "Payload") (End success)
      e0 = name "e0"
      e1 = name "e1"
  context0 <- endpointContext e0 session
  step <- mapLeft show $ sendEndpoint e0 e1 context0
  assert
    (stepMessage step == Just (MessageSpec (name "payload") (nty "Payload")))
    "send did not expose its message binder/type"
  assert
    (Map.lookup e1 (linearBindings (stepContext step)) == Just (TyEndpoint (End success)))
    "send successor endpoint has the wrong continuation"
  case consumeLinear e0 (stepContext step) of
    Left (UnknownBinding _) -> Right ()
    other -> Left ("consumed endpoint remained usable after send: " ++ show other)

testWrongPolarity :: Either String ()
testWrongPolarity = do
  let session = Send (name "payload") (nty "Payload") (End (Outcome "success"))
  context <- endpointContext (name "e0") session
  case receiveEndpoint (name "e0") (name "e1") context of
    Left (UnexpectedSessionAction ReceiveAction _) -> Right ()
    other -> Left ("receive at a send head was not rejected: " ++ show other)

testSelectProgression :: Either String ()
testSelectProgression = do
  let success = Outcome "success"
      failure = Outcome "failure"
      session = Select
        [ Branch "version" (Just (name "selected", nty "U16")) (End success)
        , Branch "unsupported" Nothing (End failure)
        ]
  context <- endpointContext (name "e0") session
  step <- mapLeft show $ selectEndpoint (name "e0") (name "e1") "version" context
  assert
    (stepMessage step == Just (MessageSpec (name "selected") (nty "U16")))
    "selected branch payload was not exposed"
  assert
    (stepSuccessor step == Just (name "e1", End success))
    "selected branch did not produce its declared continuation"

testUnknownLabel :: Either String ()
testUnknownLabel = do
  let session = Select
        [ Branch "accepted" Nothing (End (Outcome "success"))
        , Branch "rejected" Nothing (End (Outcome "failure"))
        ]
  context <- endpointContext (name "e0") session
  case selectEndpoint (name "e0") (name "e1") "bogus" context of
    Left (UnknownSessionLabel label labels) ->
      assert
        (label == "bogus" && labels == ["accepted", "rejected"])
        "unknown-label diagnostic lost the requested or declared labels"
    other -> Left ("unknown select label was not rejected: " ++ show other)

testOfferWrongPolarity :: Either String ()
testOfferWrongPolarity = do
  let session = Select [Branch "continue" Nothing (End (Outcome "success"))]
  context <- endpointContext (name "e0") session
  case offerEndpoint (name "e0") (name "e1") "continue" context of
    Left (UnexpectedSessionAction (OfferAction label) _) ->
      assert (label == "continue") "wrong offer label reported"
    other -> Left ("offer at an internal-choice head was not rejected: " ++ show other)

testCloseProgression :: Either String ()
testCloseProgression = do
  let success = Outcome "success"
      failure = Outcome "failure"
      e0 = name "e0"
  context <- endpointContext e0 (End success)
  step <- mapLeft show $ closeEndpoint e0 success context
  assert (Map.null (linearBindings (stepContext step))) "close left a successor endpoint"
  contextAgain <- endpointContext e0 (End success)
  case closeEndpoint e0 failure contextAgain of
    Left (CloseOutcomeMismatch expected actual) ->
      assert (expected == success && actual == failure) "close mismatch reported the wrong outcomes"
    other -> Left ("mismatched close outcome was not rejected: " ++ show other)

testGuardedRecursion :: Either String ()
testGuardedRecursion = do
  let x = name "X"
      loop = Rec x (Receive (name "msg") (nty "Message") (SessionVar x))
  case exposeSessionHead loop of
    Right (Receive binder messageTy continuation) -> do
      assert (binder == name "msg") "guarded recursion exposed the wrong binder"
      assert (messageTy == nty "Message") "guarded recursion exposed the wrong message type"
      assert (continuation == loop) "guarded recursive continuation did not reclose the recursion"
    other -> Left ("guarded recursion did not expose a receive head: " ++ show other)

testUnguardedRecursion :: Either String ()
testUnguardedRecursion = do
  let x = name "X"
  case exposeSessionHead (Rec x (SessionVar x)) of
    Left (UnguardedRecursion variable) -> assert (variable == x) "wrong recursion variable reported"
    other -> Left ("unguarded recursion was not rejected: " ++ show other)

testDuality :: Either String ()
testDuality = do
  let session = Send
        (name "hello")
        (nty "Frame[Hello]")
        (Select
          [ Branch "unsupported" Nothing (End (Outcome "failure"))
          , Branch "version" (Just (name "selected", nty "U16")) (End (Outcome "success"))
          ])
  assert (dualSession (dualSession session) == session) "dual . dual changed the session type"

endpointContext :: Name -> Session -> Either String ResourceContext
endpointContext endpoint session =
  mapLeft show $ insertBinding Linear endpoint (TyEndpoint session) emptyContext

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
