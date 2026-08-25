{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
  ( CallableOccurrenceKey (..)
  , CaptureOccurrenceKey (..)
  )
import Phil.Core.CallableScope
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-010 escaping closure cannot capture scoped shared loan" escapingScopedLoanRejects
    , test "CALL-010 exact-scope local closure may capture scoped shared loan" containedScopedLoanAccepts
    , test "CALL-010 local closure outside loan scope rejects" wrongContainedScopeRejects
    , test "CALL-010 scope-independent capture may escape" independentCaptureMayEscape
    , test "CALL-014 restricted self-recursive closure environment rejects" restrictedSelfCycleRejects
    , test "CALL-014 restricted mutual recursive closure environment rejects" restrictedMutualCycleRejects
    , test "CALL-014 unrestricted recursive closure environment is admitted" unrestrictedCycleAccepts
    , test "CALL-014 acyclic restricted closure environment is admitted" acyclicRestrictedAccepts
    , test "recursive closure graph rejects unknown references" unknownReferenceRejects
    , test "recursive closure graph rejects duplicate node identities" duplicateNodeRejects
    , test "restricted-cycle diagnostic is canonical under node ordering" cycleDiagnosticIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

escapingScopedLoanRejects :: Either String ()
escapingScopedLoanRejects =
  case checkClosureCaptureScope
      escapingClosure
      EscapingClosure
      [ScopedSharedLoanCapture sharedView loanScope] of
    Left (EscapingClosureCapturesScopedLoan closure capture scope) -> do
      assert (closure == escapingClosure) "diagnostic named wrong closure"
      assert (capture == sharedView) "diagnostic named wrong capture"
      assert (scope == loanScope) "diagnostic named wrong loan scope"
    other -> Left ("escaping scoped loan did not reject: " <> show other)

containedScopedLoanAccepts :: Either String ()
containedScopedLoanAccepts =
  mapLeft show $ checkClosureCaptureScope
    localClosure
    (ClosureContainedIn loanScope)
    [ScopedSharedLoanCapture sharedView loanScope]

wrongContainedScopeRejects :: Either String ()
wrongContainedScopeRejects =
  case checkClosureCaptureScope
      localClosure
      (ClosureContainedIn otherScope)
      [ScopedSharedLoanCapture sharedView loanScope] of
    Left (ClosureOutsideScopedLoanValidity closure capture expected actual) -> do
      assert (closure == localClosure) "wrong-scope diagnostic named wrong closure"
      assert (capture == sharedView) "wrong-scope diagnostic named wrong capture"
      assert (expected == loanScope) "wrong-scope diagnostic lost loan scope"
      assert (actual == otherScope) "wrong-scope diagnostic lost closure scope"
    other -> Left ("closure outside loan validity did not reject: " <> show other)

independentCaptureMayEscape :: Either String ()
independentCaptureMayEscape =
  mapLeft show $ checkClosureCaptureScope
    escapingClosure
    EscapingClosure
    [ScopeIndependentCapture ownedCapture]

restrictedSelfCycleRejects :: Either String ()
restrictedSelfCycleRejects =
  case checkRestrictedRecursiveClosureCycles [restrictedSelfNode] of
    Left (RestrictedRecursiveClosureCycle closures captures) -> do
      assert (closures == Set.singleton recursiveA)
        "self-cycle diagnostic named wrong closure set"
      assert (captures == Set.singleton restrictedCapture)
        "self-cycle diagnostic named wrong restricted capture set"
    other -> Left ("restricted self-cycle did not reject: " <> show other)

restrictedMutualCycleRejects :: Either String ()
restrictedMutualCycleRejects =
  case checkRestrictedRecursiveClosureCycles [mutualA, mutualB] of
    Left (RestrictedRecursiveClosureCycle closures captures) -> do
      assert (closures == Set.fromList [recursiveA, recursiveB])
        "mutual-cycle diagnostic named wrong closure set"
      assert (captures == Set.singleton restrictedCapture)
        "mutual-cycle diagnostic named wrong restricted capture set"
    other -> Left ("restricted mutual cycle did not reject: " <> show other)

unrestrictedCycleAccepts :: Either String ()
unrestrictedCycleAccepts =
  mapLeft show $ checkRestrictedRecursiveClosureCycles [unrestrictedSelfNode]

acyclicRestrictedAccepts :: Either String ()
acyclicRestrictedAccepts =
  mapLeft show $ checkRestrictedRecursiveClosureCycles [acyclicA, acyclicB]

unknownReferenceRejects :: Either String ()
unknownReferenceRejects =
  case checkRestrictedRecursiveClosureCycles [unknownReferenceNode] of
    Left (UnknownRecursiveClosureReference source target) -> do
      assert (source == recursiveA) "unknown-reference diagnostic named wrong source"
      assert (target == missingClosure) "unknown-reference diagnostic named wrong target"
    other -> Left ("unknown recursive reference did not reject: " <> show other)

duplicateNodeRejects :: Either String ()
duplicateNodeRejects =
  case checkRestrictedRecursiveClosureCycles [acyclicA, acyclicA] of
    Left (DuplicateRecursiveClosureNode key) ->
      assert (key == recursiveA) "duplicate-node diagnostic named wrong closure"
    other -> Left ("duplicate recursion node did not reject: " <> show other)

cycleDiagnosticIsCanonical :: Either String ()
cycleDiagnosticIsCanonical = do
  let left = checkRestrictedRecursiveClosureCycles [mutualA, mutualB]
      right = checkRestrictedRecursiveClosureCycles [mutualB, mutualA]
  assert (left == right) "node enumeration order changed recursive-cycle diagnostic"

restrictedSelfNode :: ClosureRecursionNode
restrictedSelfNode = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveA
  , closureRecursionReferences = Set.singleton recursiveA
  , closureRecursionRestrictedCaptures = Set.singleton restrictedCapture
  }

unrestrictedSelfNode :: ClosureRecursionNode
unrestrictedSelfNode = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveA
  , closureRecursionReferences = Set.singleton recursiveA
  , closureRecursionRestrictedCaptures = Set.empty
  }

mutualA, mutualB :: ClosureRecursionNode
mutualA = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveA
  , closureRecursionReferences = Set.singleton recursiveB
  , closureRecursionRestrictedCaptures = Set.singleton restrictedCapture
  }

mutualB = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveB
  , closureRecursionReferences = Set.singleton recursiveA
  , closureRecursionRestrictedCaptures = Set.empty
  }

acyclicA, acyclicB :: ClosureRecursionNode
acyclicA = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveA
  , closureRecursionReferences = Set.singleton recursiveB
  , closureRecursionRestrictedCaptures = Set.singleton restrictedCapture
  }

acyclicB = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveB
  , closureRecursionReferences = Set.empty
  , closureRecursionRestrictedCaptures = Set.empty
  }

unknownReferenceNode :: ClosureRecursionNode
unknownReferenceNode = ClosureRecursionNode
  { closureRecursionOccurrence = recursiveA
  , closureRecursionReferences = Set.singleton missingClosure
  , closureRecursionRestrictedCaptures = Set.empty
  }

escapingClosure, localClosure, recursiveA, recursiveB, missingClosure
  :: CallableOccurrenceKey
escapingClosure = CallableOccurrenceKey "closure.escape.001"
localClosure = CallableOccurrenceKey "closure.local.001"
recursiveA = CallableOccurrenceKey "closure.recursive.a"
recursiveB = CallableOccurrenceKey "closure.recursive.b"
missingClosure = CallableOccurrenceKey "closure.recursive.missing"

sharedView, ownedCapture, restrictedCapture :: CaptureOccurrenceKey
sharedView = CaptureOccurrenceKey "loan.view.001"
ownedCapture = CaptureOccurrenceKey "owner.bytes.010"
restrictedCapture = CaptureOccurrenceKey "owner.linear.recursive.001"

loanScope, otherScope :: LoanScopeKey
loanScope = LoanScopeKey "scope.loan.001"
otherScope = LoanScopeKey "scope.other.001"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
