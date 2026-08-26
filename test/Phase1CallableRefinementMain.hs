{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Callable
import Phil.Core.CallableRefinement
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Outcome (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-012 exact semantic callable refinement accepts" exactSemanticRefinementAccepts
    , test "CALL-012 distinct interface revisions may be related by checked refinement" distinctRevisionsMayRefine
    , test "CALL-012 matching machine shape is insufficient for stronger authority" strongerAuthorityRejects
    , test "CALL-012 matching machine shape is insufficient for wider effects" widerEffectsReject
    , test "CALL-012 matching machine shape is insufficient for extra fatal outcomes" extraFatalRejects
    , test "CALL-012 incompatible callee transitions reject" incompatibleTransitionRejects
    , test "CALL-012 replace payload mismatch rejects even with the same transition kind" replacePayloadMismatchRejects
    , test "CALL-012 semantically narrower actual is accepted" narrowerActualAccepts
    , test "CALL-012 machine-shape mismatch still rejects" machineShapeMismatchRejects
    , test "CALL-012 widening diagnostics are canonical under set ordering" wideningDiagnosticsAreCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactSemanticRefinementAccepts :: Either String ()
exactSemanticRefinementAccepts = do
  checked <- mapLeft show $ checkCallableRefinement expectedSurface exactActualSurface
  assert
    (checkedCallableRefinementExpected checked == expectedSurface)
    "checked refinement did not retain expected callable surface"
  assert
    (checkedCallableRefinementActual checked == exactActualSurface)
    "checked refinement did not retain actual callable surface"

distinctRevisionsMayRefine :: Either String ()
distinctRevisionsMayRefine = do
  _ <- mapLeft show $ checkCallableRefinement expectedSurface exactActualSurface
  assert
    ( callableContractInterfaceRevision (callableRefinementContract expectedSurface)
        /= callableContractInterfaceRevision (callableRefinementContract exactActualSurface) )
    "fixture did not exercise distinct callable interface revisions"

strongerAuthorityRejects :: Either String ()
strongerAuthorityRejects =
  case checkCallableRefinement expectedSurface strongerAuthorityActual of
    Left (CallableAuthorityRequirementTooStrong excess) ->
      assert (excess == Set.singleton deleteAuthority)
        "authority diagnostic did not report exact excess authority"
    other -> Left ("stronger authority requirement did not reject: " <> show other)

widerEffectsReject :: Either String ()
widerEffectsReject =
  case checkCallableRefinement expectedSurface widerEffectActual of
    Left (CallableEffectBoundTooWide excess) ->
      assert (excess == Set.singleton deleteEffect)
        "effect diagnostic did not report exact excess effect"
    other -> Left ("wider effect bound did not reject: " <> show other)

extraFatalRejects :: Either String ()
extraFatalRejects =
  case checkCallableRefinement expectedSurface fatalActual of
    Left (CallableFailureSetTooWide excess) ->
      assert (excess == Set.singleton fatalAbort)
        "failure diagnostic did not report exact extra fatal outcome"
    other -> Left ("extra fatal outcome did not reject: " <> show other)

incompatibleTransitionRejects :: Either String ()
incompatibleTransitionRejects =
  case checkCallableRefinement expectedSurface consumingActual of
    Left (CallableCalleeTransitionIncompatible expected actual) -> do
      assert (expected == PreserveCallee) "wrong expected callee transition"
      assert (actual == ConsumeCallee) "wrong actual callee transition"
    other -> Left ("incompatible callee transition did not reject: " <> show other)

replacePayloadMismatchRejects :: Either String ()
replacePayloadMismatchRejects =
  case checkCallableRefinement replaceExpectedSurface replaceActualSurface of
    Left (CallableCalleeTransitionIncompatible expected actual) -> do
      assert
        (expected == ReplaceCallee successorRevision (Just successorStateA))
        "wrong expected replacement payload"
      assert
        (actual == ReplaceCallee successorRevision (Just successorStateB))
        "wrong actual replacement payload"
    other -> Left ("replace payload mismatch did not reject: " <> show other)

narrowerActualAccepts :: Either String ()
narrowerActualAccepts = do
  _ <- mapLeft show $ checkCallableRefinement richExpectedSurface narrowActualSurface
  Right ()

machineShapeMismatchRejects :: Either String ()
machineShapeMismatchRejects =
  case checkCallableRefinement expectedSurface wrongShapeActual of
    Left (CallableMachineShapeMismatch expected actual) -> do
      assert (expected == byteCallableShape) "wrong expected machine shape"
      assert (actual == scalarCallableShape) "wrong actual machine shape"
    other -> Left ("machine-shape mismatch did not reject: " <> show other)

wideningDiagnosticsAreCanonical :: Either String ()
wideningDiagnosticsAreCanonical =
  let left = checkCallableRefinement expectedSurface
        (exactActualSurface
          { callableRefinementCallerAuthority =
              Set.fromList [deleteAuthority, overwriteAuthority, readAuthority]
          })
      right = checkCallableRefinement expectedSurface
        (exactActualSurface
          { callableRefinementCallerAuthority =
              Set.fromList [readAuthority, overwriteAuthority, deleteAuthority]
          })
  in assert (left == right)
      "authority widening diagnostic depended on source enumeration order"

byteCallableShape, scalarCallableShape :: CallableMachineShape
byteCallableShape = CallableMachineShape "bytes -> result"
scalarCallableShape = CallableMachineShape "u64 -> result"

readAuthority, auditAuthority, deleteAuthority, overwriteAuthority
  :: CallableAuthorityRequirement
readAuthority = CallableAuthorityRequirement "storage.read"
auditAuthority = CallableAuthorityRequirement "audit.append"
deleteAuthority = CallableAuthorityRequirement "storage.delete"
overwriteAuthority = CallableAuthorityRequirement "storage.overwrite"

readEffect, auditEffect, deleteEffect :: SemanticEffect
readEffect = SemanticEffect "read"
auditEffect = SemanticEffect "audit"
deleteEffect = SemanticEffect "delete"

notFoundFailure, terminalShutdown, fatalAbort :: CallableFailure
notFoundFailure = CallableTypedNegative (Outcome "not-found")
terminalShutdown = CallableDeclaredTerminal (Outcome "shutdown")
fatalAbort = CallableFatal "abort"

successorRevision :: InterfaceRevision
successorRevision = InterfaceRevision "callable.successor.v1"

successorStateA, successorStateB :: CallableStateKey
successorStateA = CallableStateKey "state-a"
successorStateB = CallableStateKey "state-b"

expectedContract, exactActualContract, richExpectedContract, narrowActualContract,
  replaceExpectedContract, replaceActualContract :: CallableContract
expectedContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.expected.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton readEffect
  }

exactActualContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.actual.v7"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton readEffect
  }

richExpectedContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.rich-expected.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.fromList [readEffect, auditEffect]
  }

narrowActualContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.narrow-actual.v3"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.singleton readEffect
  }

replaceExpectedContract = exactActualContract
  { callableContractCalleeTransition =
      ReplaceCallee successorRevision (Just successorStateA)
  }

replaceActualContract = exactActualContract
  { callableContractCalleeTransition =
      ReplaceCallee successorRevision (Just successorStateB)
  }

expectedSurface, exactActualSurface, richerFailureSurface,
  replaceExpectedSurface, replaceActualSurface :: CallableRefinementSurface
expectedSurface = CallableRefinementSurface
  { callableRefinementMachineShape = byteCallableShape
  , callableRefinementContract = expectedContract
  , callableRefinementCallerAuthority = Set.singleton readAuthority
  , callableRefinementFailures = Set.singleton notFoundFailure
  }

exactActualSurface = CallableRefinementSurface
  { callableRefinementMachineShape = byteCallableShape
  , callableRefinementContract = exactActualContract
  , callableRefinementCallerAuthority = Set.singleton readAuthority
  , callableRefinementFailures = Set.singleton notFoundFailure
  }

richerFailureSurface = expectedSurface
  { callableRefinementFailures = Set.fromList [notFoundFailure, terminalShutdown] }

replaceExpectedSurface = exactActualSurface
  { callableRefinementContract = replaceExpectedContract }

replaceActualSurface = exactActualSurface
  { callableRefinementContract = replaceActualContract }

strongerAuthorityActual, widerEffectActual, fatalActual, consumingActual,
  wrongShapeActual, richExpectedSurface, narrowActualSurface :: CallableRefinementSurface
strongerAuthorityActual = exactActualSurface
  { callableRefinementCallerAuthority = Set.fromList [readAuthority, deleteAuthority] }

widerEffectActual = exactActualSurface
  { callableRefinementContract = exactActualContract
      { callableContractEffectBound = Set.fromList [readEffect, deleteEffect] }
  }

fatalActual = exactActualSurface
  { callableRefinementFailures = Set.fromList [notFoundFailure, fatalAbort] }

consumingActual = exactActualSurface
  { callableRefinementContract = exactActualContract
      { callableContractCalleeTransition = ConsumeCallee }
  }

wrongShapeActual = exactActualSurface
  { callableRefinementMachineShape = scalarCallableShape }

richExpectedSurface = richerFailureSurface
  { callableRefinementContract = richExpectedContract
  , callableRefinementCallerAuthority = Set.fromList [readAuthority, auditAuthority]
  }

narrowActualSurface = exactActualSurface
  { callableRefinementContract = narrowActualContract }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
