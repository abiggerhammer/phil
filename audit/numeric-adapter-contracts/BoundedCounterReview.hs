{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM_, unless)
import qualified NumericFixture as N
import qualified PingFixture as F
import Phil.Core.Authority (AuthorityState, AuthorityExerciseSource (..), emptyAuthorityState)
import qualified Phil.Core.NumericConversion as C
import Phil.Core.ProcessActivation (ActivationOccurrenceKey (..))
import Phil.Core.ProcessRendezvous (ProcessCommunicationState)
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Syntax (Ty (..))
import Phil.IO.Console (ConsoleWriteOutcome (..))
import qualified Phil.Surface.GrammarV1.BoundedPingLoopSource as L
import qualified Phil.Surface.GrammarV1.BoundedPingRuntime as P
import System.Exit (exitFailure)

-- All positive plans, process state, checked loop/source and provisioning come
-- from the unchanged permanent sourceFixture (namespace-only adaptation).
-- Root numeric values and the conversion-to-root carrier join are explicit
-- audit inputs. No accepted plan, ValueResult, proof or runtime evidence is
-- manufactured or edited. Console outcome is a declared fixture input; these
-- pure runtime-model calls do not perform native I/O or execute emitted code.

type RuntimeResult = Either P.GrammarV1BoundedPingRuntimeError
  (ProcessCommunicationState, P.GrammarV1BoundedPingRuntimeEvidence)

runAt :: F.Fixture -> AuthorityState -> ActivationOccurrenceKey -> ScalarLiteral
  -> Either String RuntimeResult
runAt fx authority occurrence literal = do
  values <- F.roundValuesFromSource F.roundSource
  pure $ P.grammarV1RunBoundedPingFromSource
    (F.fixtureInstance fx) (F.fixtureNetwork fx) (F.fixtureCommunication fx)
    (F.fixturePlan fx) (P.GrammarV1RootCountValue occurrence literal) values
    (PossessedCapability F.stdoutCapability) authority ConsoleWriteSucceeded

runCount :: F.Fixture -> AuthorityState -> ScalarLiteral -> Either String RuntimeResult
runCount fx authority literal =
  runAt fx authority (P.boundedPingRuntimeCountOccurrence (F.fixturePlan fx)) literal

smallCounts :: Either String ()
smallCounts = do
  fx <- F.sourceFixture
  authority <- F.stdoutAuthority
  forM_ [0..6] $ \count -> do
    result <- runCount fx authority (ScalarUIntLiteral 32 count)
    (closed,evidence) <- N.right result
    let rounds = P.boundedPingEvidenceIterations evidence
        before = reverse [1..count]
        after = reverse [0..count-1]
        plan = F.fixturePlan fx
    N.same (fromInteger count) (length rounds)
    N.same [0..fromInteger count-1] (map P.boundedPingIterationIndex rounds)
    N.same before (map P.boundedPingIterationRemainingBefore rounds)
    N.same after (map P.boundedPingIterationRemainingAfter rounds)
    N.same count (P.boundedPingEvidenceInitialCount evidence)
    N.same (P.boundedPingRuntimeCountOccurrence plan) (P.boundedPingEvidenceCountOccurrence evidence)
    N.same (L.boundedPingCountState (P.boundedPingRuntimeLoopSource plan))
      (P.boundedPingEvidenceCountStateBinder evidence)
    N.ensure (all ((== ScalarUIntLiteral 8 42) . P.boundedPingIterationRequestValue) rounds)
      "checked source request changed"
    N.ensure (all ((== "pong") . P.boundedPingIterationReplyText) rounds)
      "checked source reply changed"
    F.assertBackedgeChain rounds
    F.assertClosedAndTerminal fx closed evidence

convertedCount :: Either String ()
convertedCount = do
  fx <- F.sourceFixture
  authority <- F.stdoutAuthority
  original <- N.uintLeaf 8 "3"
  converted <- N.right $ C.convertNumericValue (C.NumericUIntType 32) original
  N.same C.NumericConversionExact (C.numericConversionPrecision converted)
  literal <- case C.numericConversionValue converted of
    C.NumericUIntValue width value -> Right (ScalarUIntLiteral width value)
    other -> Left ("unexpected actual converted domain: " <> show other)
  result <- runCount fx authority literal
  (closed,evidence) <- N.right result
  N.same [3,2,1] (map P.boundedPingIterationRemainingBefore (P.boundedPingEvidenceIterations evidence))
  N.same [2,1,0] (map P.boundedPingIterationRemainingAfter (P.boundedPingEvidenceIterations evidence))
  F.assertClosedAndTerminal fx closed evidence

wrongOccurrence :: Either String ()
wrongOccurrence = do
  fx <- F.sourceFixture
  authority <- F.stdoutAuthority
  let actual = ActivationOccurrenceKey "independent.other-count-occurrence"
      expected = P.boundedPingRuntimeCountOccurrence (F.fixturePlan fx)
  result <- runAt fx authority actual (ScalarUIntLiteral 32 3)
  N.same (Left (P.GrammarV1BoundedPingRuntimeCountOccurrenceMismatch expected actual)) result

wrongWidth :: Either String ()
wrongWidth = do
  fx <- F.sourceFixture
  authority <- F.stdoutAuthority
  value <- N.uintLeaf 16 "3"
  literal <- case value of
    C.NumericUIntValue width magnitude -> Right (ScalarUIntLiteral width magnitude)
    other -> Left ("unexpected contextually admitted domain: " <> show other)
  result <- runCount fx authority literal
  N.same (Left (P.GrammarV1BoundedPingRuntimeScalarTypeMismatch (TyUInt 32) (TyUInt 16))) result

outOfRange :: Either String ()
outOfRange = do
  fx <- F.sourceFixture
  authority <- F.stdoutAuthority
  -- This is the external runtime scalar admission boundary, not a manufactured
  -- malformed numeric evaluator environment. Neither value may enter the loop.
  forM_ [-1, 4294967296] $ \value -> do
    let literal = ScalarUIntLiteral 32 value
    result <- runCount fx authority literal
    N.same (Left (P.GrammarV1BoundedPingRuntimeScalarOutOfRange literal)) result

zeroNeedsNoUnusedOutputAuthority :: Either String ()
zeroNeedsNoUnusedOutputAuthority = do
  fx <- F.sourceFixture
  result <- runCount fx emptyAuthorityState (ScalarUIntLiteral 32 0)
  (closed,evidence) <- N.right result
  N.same [] (P.boundedPingEvidenceIterations evidence)
  F.assertClosedAndTerminal fx closed evidence

main :: IO ()
main = do
  results <- sequence
    [ test "P01" "source-provisioned counts zero through six retain exact successor chains" smallCounts
    , test "P02" "actual admitted and converted U32 payload is the runtime initial count" convertedCount
    , test "P03" "source-aware runtime rejects a different activation-bound count" wrongOccurrence
    , test "P04" "valid contextually admitted U16 is not silently widened at U32 entry" wrongWidth
    , test "P05" "out-of-range external count rejects before recursive execution" outOfRange
    , test "P06" "zero count closes without requiring unused output authority" zeroNeedsNoUnusedOutputAuthority
    ]
  putStrLn "COMPLETE bounded_counter_groups=6"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
