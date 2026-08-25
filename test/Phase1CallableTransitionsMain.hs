{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-006 PreserveCallee retains one linear closure occurrence" preserveLinearOccurrence
    , test "CALL-006 preserved linear closure may be invoked repeatedly" preserveLinearRepeatedly
    , test "CALL-007 PreserveCallee rejects missing restricted capture residue" preserveRejectsConsumedCapture
    , test "CALL-007 PreserveCallee rejects an invented successor" preserveRejectsSuccessor
    , test "CALL-008 ConsumeCallee removes one-shot occurrence" consumeRemovesOccurrence
    , test "CALL-008 consumed predecessor cannot be invoked again" consumeRejectsReuse
    , test "CALL-008 ConsumeCallee rejects an undeclared successor" consumeRejectsSuccessor
    , test "CALL-009 ReplaceCallee installs exact distinct successor" replaceInstallsSuccessor
    , test "CALL-009 predecessor remains unavailable after equal-contract replacement" replaceRejectsStalePredecessor
    , test "CALL-009 replacement may preserve public callable interface" replaceMayKeepInterface
    , test "CALL-009 replacement rejects predecessor-key resurrection" replaceRejectsSameOccurrenceKey
    , test "CALL-009 replacement rejects wrong successor interface" replaceRejectsWrongInterface
    , test "CALL-009 replacement rejects wrong successor state" replaceRejectsWrongState
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

preserveLinearOccurrence :: Either String ()
preserveLinearOccurrence = do
  after <- mapLeft show $ invokeCallableOccurrence
    linearPreservedKey
    preservedBody
    (singletonCallableResourceState linearPreservedOccurrence)
  assert
    (lookupCallableOccurrence linearPreservedKey after == Just linearPreservedOccurrence)
    "PreserveCallee changed or removed the exact linear callable occurrence"

preserveLinearRepeatedly :: Either String ()
preserveLinearRepeatedly = do
  once <- mapLeft show $ invokeCallableOccurrence
    linearPreservedKey
    preservedBody
    (singletonCallableResourceState linearPreservedOccurrence)
  twice <- mapLeft show $ invokeCallableOccurrence
    linearPreservedKey
    preservedBody
    once
  assert
    (lookupCallableOccurrence linearPreservedKey twice == Just linearPreservedOccurrence)
    "second preserving invocation lost the unique closure owner"

preserveRejectsConsumedCapture :: Either String ()
preserveRejectsConsumedCapture =
  case invokeCallableOccurrence
      linearPreservedKey
      emptyBody
      (singletonCallableResourceState linearPreservedOccurrence) of
    Left (PreserveCalleeRestrictedStateMismatch key expected actual) -> do
      assert (key == linearPreservedKey) "preserve diagnostic named wrong callable"
      assert (expected == Set.singleton capturedOwnerKey)
        "preserve diagnostic lost required capture identity"
      assert (Set.null actual) "preserve diagnostic invented actual residue"
    other -> Left ("missing preserved capture did not reject: " <> show other)

preserveRejectsSuccessor :: Either String ()
preserveRejectsSuccessor =
  case invokeCallableOccurrence
      linearPreservedKey
      preservedBody { invocationSuccessorCallable = Just replacementSuccessor }
      (singletonCallableResourceState linearPreservedOccurrence) of
    Left (PreserveCalleeProducedSuccessor predecessor successor) -> do
      assert (predecessor == linearPreservedKey) "wrong preserve predecessor"
      assert (successor == replacementSuccessorKey) "wrong preserve successor"
    other -> Left ("preserving invocation accepted successor: " <> show other)

consumeRemovesOccurrence :: Either String ()
consumeRemovesOccurrence = do
  after <- mapLeft show $ invokeCallableOccurrence
    oneShotKey
    emptyBody
    (singletonCallableResourceState oneShotOccurrence)
  assert
    (lookupCallableOccurrence oneShotKey after == Nothing)
    "ConsumeCallee left predecessor callable available"

consumeRejectsReuse :: Either String ()
consumeRejectsReuse = do
  after <- mapLeft show $ invokeCallableOccurrence
    oneShotKey
    emptyBody
    (singletonCallableResourceState oneShotOccurrence)
  case invokeCallableOccurrence oneShotKey emptyBody after of
    Left (UnavailableCallableOccurrence key) ->
      assert (key == oneShotKey) "stale-use diagnostic named wrong occurrence"
    other -> Left ("consumed callable was reusable: " <> show other)

consumeRejectsSuccessor :: Either String ()
consumeRejectsSuccessor =
  case invokeCallableOccurrence
      oneShotKey
      emptyBody { invocationSuccessorCallable = Just replacementSuccessor }
      (singletonCallableResourceState oneShotOccurrence) of
    Left (ConsumeCalleeProducedSuccessor predecessor successor) -> do
      assert (predecessor == oneShotKey) "wrong consume predecessor"
      assert (successor == replacementSuccessorKey) "wrong consume successor"
    other -> Left ("ConsumeCallee accepted undeclared successor: " <> show other)

replaceInstallsSuccessor :: Either String ()
replaceInstallsSuccessor = do
  after <- replacementState
  assert
    (lookupCallableOccurrence replacementPredecessorKey after == Nothing)
    "ReplaceCallee retained predecessor occurrence"
  assert
    (lookupCallableOccurrence replacementSuccessorKey after == Just replacementSuccessor)
    "ReplaceCallee did not install exact successor occurrence"

replaceRejectsStalePredecessor :: Either String ()
replaceRejectsStalePredecessor = do
  after <- replacementState
  case invokeCallableOccurrence replacementPredecessorKey replacementBody after of
    Left (UnavailableCallableOccurrence key) ->
      assert (key == replacementPredecessorKey) "wrong stale predecessor diagnostic"
    other -> Left ("replacement resurrected stale predecessor: " <> show other)

replaceMayKeepInterface :: Either String ()
replaceMayKeepInterface =
  assert
    ( callableContractInterfaceRevision (callableOccurrenceContract replacementPredecessor)
        == callableContractInterfaceRevision (callableOccurrenceContract replacementSuccessor) )
    "test fixture did not exercise equal-interface successor replacement"

replaceRejectsSameOccurrenceKey :: Either String ()
replaceRejectsSameOccurrenceKey =
  let badSuccessor = replacementSuccessor
        { callableOccurrenceKey = replacementPredecessorKey }
      badBody = replacementBody
        { invocationSuccessorCallable = Just badSuccessor }
  in case invokeCallableOccurrence
      replacementPredecessorKey
      badBody
      (singletonCallableResourceState replacementPredecessor) of
    Left (ReplaceCalleeReusedPredecessorKey key) ->
      assert (key == replacementPredecessorKey) "wrong reused-key diagnostic"
    other -> Left ("replacement reused predecessor key: " <> show other)

replaceRejectsWrongInterface :: Either String ()
replaceRejectsWrongInterface =
  let badContract = replacementContract
        { callableContractInterfaceRevision = InterfaceRevision "callable.stream.other.v1" }
      badSuccessor = replacementSuccessor
        { callableOccurrenceContract = badContract }
      badBody = replacementBody
        { invocationSuccessorCallable = Just badSuccessor }
  in case invokeCallableOccurrence
      replacementPredecessorKey
      badBody
      (singletonCallableResourceState replacementPredecessor) of
    Left (ReplaceCalleeInterfaceMismatch expected actual) -> do
      assert (expected == streamInterface) "wrong expected successor interface"
      assert (actual == InterfaceRevision "callable.stream.other.v1")
        "wrong actual successor interface"
    other -> Left ("wrong-interface successor did not reject: " <> show other)

replaceRejectsWrongState :: Either String ()
replaceRejectsWrongState =
  let badSuccessor = replacementSuccessor
        { callableOccurrenceStateKey = Just (CallableStateKey "stream.S2") }
      badBody = replacementBody
        { invocationSuccessorCallable = Just badSuccessor }
  in case invokeCallableOccurrence
      replacementPredecessorKey
      badBody
      (singletonCallableResourceState replacementPredecessor) of
    Left (ReplaceCalleeStateMismatch expected actual) -> do
      assert (expected == Just successorState) "wrong expected successor state"
      assert (actual == Just (CallableStateKey "stream.S2"))
        "wrong actual successor state"
    other -> Left ("wrong-state successor did not reject: " <> show other)

replacementState :: Either String CallableResourceState
replacementState = mapLeft show $ invokeCallableOccurrence
  replacementPredecessorKey
  replacementBody
  (singletonCallableResourceState replacementPredecessor)

preservedBody, emptyBody, replacementBody :: CallableInvocationBodySummary
preservedBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.singleton capturedOwnerKey
  , invocationSuccessorCallable = Nothing
  }

emptyBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Nothing
  }

replacementBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Just replacementSuccessor
  }

capturedOwnerKey :: CaptureOccurrenceKey
capturedOwnerKey = CaptureOccurrenceKey "owner.bytes.006"

linearCaptureSummary :: ClosureCaptureSummary
linearCaptureSummary = case checkClosureCaptures
    [ClosureCapture capturedOwnerKey MoveCapture Linear] of
  Right summary -> summary
  Left err -> error (show err)

emptyCaptureSummary :: ClosureCaptureSummary
emptyCaptureSummary = case checkClosureCaptures [] of
  Right summary -> summary
  Left err -> error (show err)

linearPreservedKey, oneShotKey, replacementPredecessorKey, replacementSuccessorKey
  :: CallableOccurrenceKey
linearPreservedKey = CallableOccurrenceKey "callable.linear-preserved.001"
oneShotKey = CallableOccurrenceKey "callable.one-shot.001"
replacementPredecessorKey = CallableOccurrenceKey "callable.stream.001"
replacementSuccessorKey = CallableOccurrenceKey "callable.stream.002"

successorState :: CallableStateKey
successorState = CallableStateKey "stream.S1"

streamInterface :: InterfaceRevision
streamInterface = InterfaceRevision "callable.stream.interface.v1"

preserveLinearContract, oneShotContract, replacementContract :: CallableContract
preserveLinearContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.linear-preserved.interface.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.empty
  }

oneShotContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.one-shot.interface.v1"
  , callableContractCalleeTransition = ConsumeCallee
  , callableContractEffectBound = Set.empty
  }

replacementContract = CallableContract
  { callableContractInterfaceRevision = streamInterface
  , callableContractCalleeTransition = ReplaceCallee streamInterface (Just successorState)
  , callableContractEffectBound = Set.empty
  }

linearPreservedOccurrence, oneShotOccurrence, replacementPredecessor, replacementSuccessor
  :: CallableOccurrence
linearPreservedOccurrence = CallableOccurrence
  { callableOccurrenceKey = linearPreservedKey
  , callableOccurrenceContract = preserveLinearContract
  , callableOccurrenceCaptures = linearCaptureSummary
  , callableOccurrenceStateKey = Nothing
  }

oneShotOccurrence = CallableOccurrence
  { callableOccurrenceKey = oneShotKey
  , callableOccurrenceContract = oneShotContract
  , callableOccurrenceCaptures = emptyCaptureSummary
  , callableOccurrenceStateKey = Nothing
  }

replacementPredecessor = CallableOccurrence
  { callableOccurrenceKey = replacementPredecessorKey
  , callableOccurrenceContract = replacementContract
  , callableOccurrenceCaptures = emptyCaptureSummary
  , callableOccurrenceStateKey = Just (CallableStateKey "stream.S0")
  }

replacementSuccessor = CallableOccurrence
  { callableOccurrenceKey = replacementSuccessorKey
  , callableOccurrenceContract = replacementContract
  , callableOccurrenceCaptures = emptyCaptureSummary
  , callableOccurrenceStateKey = Just successorState
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
