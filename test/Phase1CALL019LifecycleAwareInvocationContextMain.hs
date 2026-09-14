{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationLifecycleContext (..)
  , SurfaceCallableCallerContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
  )
import Phil.Compiler.CallableInvocationLifecycle
  ( SurfaceCallableInvocationLifecycleBinding (..)
  , SurfaceCallableInvocationLifecycleError (..)
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  , CallableContract (..)
  , CallableInvocationBodySummary (..)
  , CallableOccurrence (..)
  , CallableOccurrenceKey (..)
  , CallableResourceState
  , CallableStateKey (..)
  , checkClosureCaptures
  , lookupCallableOccurrence
  , singletonCallableResourceState
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 legacy branch-aware admission still rejects ConsumeCallee"
        legacyConsumeStillRejects
    , test "CALL-019 lifecycle-aware admission executes ConsumeCallee"
        lifecycleConsumeAccepts
    , test "CALL-019 lifecycle-aware admission executes ReplaceCallee"
        lifecycleReplaceAccepts
    , test "CALL-019 lifecycle-aware admission requires exact lifecycle binding domain"
        missingLifecycleBindingRejects
    , test "CALL-019 lifecycle-aware admission rejects concrete transition substitution"
        concreteTransitionSubstitutionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

invocationSpan :: SourceSpan
invocationSpan = SourceSpan
  (SourcePoint "call019-lifecycle-context" 1 1 0)
  (SourcePoint "call019-lifecycle-context" 1 8 7)

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.lifecycle.worker"

consumeKey, preserveKey, replacePredecessorKey, replaceSuccessorKey :: CallableOccurrenceKey
consumeKey = CallableOccurrenceKey "callable.consume.001"
preserveKey = CallableOccurrenceKey "callable.preserve.001"
replacePredecessorKey = CallableOccurrenceKey "callable.replace.001"
replaceSuccessorKey = CallableOccurrenceKey "callable.replace.002"

replaceInterface :: InterfaceRevision
replaceInterface = InterfaceRevision "callable.replace.v1"

replaceState :: CallableStateKey
replaceState = CallableStateKey "replace.S1"

emptyCaptures :: Either String Phil.Core.Callable.ClosureCaptureSummary
emptyCaptures = mapLeft show (checkClosureCaptures [])

contract :: InterfaceRevision -> CalleeTransition -> CallableContract
contract revision transition = CallableContract
  { callableContractInterfaceRevision = revision
  , callableContractCalleeTransition = transition
  , callableContractEffectBound = Set.empty
  }

consumeContract, preserveContract, replaceContract :: CallableContract
consumeContract = contract (InterfaceRevision "callable.consume.v1") ConsumeCallee
preserveContract = contract (InterfaceRevision "callable.preserve.v1") PreserveCallee
replaceContract = contract replaceInterface (ReplaceCallee replaceInterface (Just replaceState))

occurrence
  :: CallableOccurrenceKey
  -> CallableContract
  -> Maybe CallableStateKey
  -> Either String CallableOccurrence
occurrence key callableContract stateKey = do
  captures <- emptyCaptures
  Right CallableOccurrence
    { callableOccurrenceKey = key
    , callableOccurrenceContract = callableContract
    , callableOccurrenceCaptures = captures
    , callableOccurrenceStateKey = stateKey
    }

consumeOccurrence, preserveOccurrence, replacePredecessor, replaceSuccessor
  :: Either String CallableOccurrence
consumeOccurrence = occurrence consumeKey consumeContract Nothing
preserveOccurrence = occurrence preserveKey preserveContract Nothing
replacePredecessor = occurrence
  replacePredecessorKey replaceContract (Just (CallableStateKey "replace.S0"))
replaceSuccessor = occurrence replaceSuccessorKey replaceContract (Just replaceState)

bodyWithoutSuccessor :: CallableInvocationBodySummary
bodyWithoutSuccessor = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Nothing
  }

replaceBody :: Either String CallableInvocationBodySummary
replaceBody = do
  successor <- replaceSuccessor
  Right CallableInvocationBodySummary
    { invocationRestrictedCaptureResidue = Set.empty
    , invocationSuccessorCallable = Just successor
    }

successOutcome :: CalleeTransition -> CallableOutcomeContract
successOutcome transition = CallableOutcomeContract
  { callableOutcomeClass = CallableSuccessOutcome
  , callableOutcomeState = CallableOutcomeState "success"
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

account :: CalleeTransition -> SurfaceCallableInvocationSemanticAccount
account transition = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "LifecycleWorker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = transition
  , surfaceSemanticInvocationModeledFailures = Set.empty
  , surfaceSemanticInvocationOutcomes = [successOutcome transition]
  }

summary :: CalleeTransition -> SurfaceCallableSemanticSummary
summary transition = SurfaceCallableSemanticSummary
  { surfaceCallableSemanticAccounts = [account transition]
  , surfaceReachableCallableEffects = Set.empty
  , surfaceRequiredCallerAuthority = Set.empty
  , surfaceReachableCallableFailures = Set.empty
  }

callerContext :: SurfaceCallableCallerContext
callerContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority = Set.empty
  , surfaceCallerPublicContract = CallableRefinementSurface
      { callableRefinementMachineShape = CallableMachineShape "Caller"
      , callableRefinementContract = contract (InterfaceRevision "caller.v1") PreserveCallee
      , callableRefinementCallerAuthority = Set.empty
      , callableRefinementFailures = Set.empty
      }
  }

binding
  :: CallableOccurrenceKey
  -> CallableInvocationBodySummary
  -> SurfaceCallableInvocationLifecycleBinding
binding predecessor body = SurfaceCallableInvocationLifecycleBinding
  { surfaceLifecycleBindingInvocationSpan = invocationSpan
  , surfaceLifecycleBindingDeclarationKey = workerKey
  , surfaceLifecycleBindingPredecessor = predecessor
  , surfaceLifecycleBindingBodySummary = body
  }

bindingMap
  :: SurfaceCallableInvocationLifecycleBinding
  -> Map.Map (SourceSpan, DeclarationKey) SurfaceCallableInvocationLifecycleBinding
bindingMap value = Map.singleton (invocationSpan, workerKey) value

legacyConsumeStillRejects :: Either String ()
legacyConsumeStillRejects =
  case checkSurfaceCallableInvocationSummaryWithOutcomeBranches
      [] callerContext (summary ConsumeCallee) of
    Left (SurfaceInvocationDirectCalleeTransitionUnsupported actualSpan ConsumeCallee)
      | actualSpan == invocationSpan -> Right ()
    Left other -> Left ("wrong legacy lifecycle rejection: " <> show other)
    Right accepted -> Left ("legacy branch-aware context accepted ConsumeCallee: " <> show accepted)

lifecycleConsumeAccepts :: Either String ()
lifecycleConsumeAccepts = do
  initialOccurrence <- consumeOccurrence
  let initialState = singletonCallableResourceState initialOccurrence
  checked <- mapLeft show $
    checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
      (bindingMap (binding consumeKey bodyWithoutSuccessor))
      initialState
      []
      callerContext
      (summary ConsumeCallee)
  assert
    (lookupCallableOccurrence consumeKey
      (checkedInvocationFinalCallableState checked) == Nothing)
    "ConsumeCallee lifecycle witness left predecessor available"

lifecycleReplaceAccepts :: Either String ()
lifecycleReplaceAccepts = do
  predecessor <- replacePredecessor
  successor <- replaceSuccessor
  replacementBody <- replaceBody
  checked <- mapLeft show $
    checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
      (bindingMap (binding replacePredecessorKey replacementBody))
      (singletonCallableResourceState predecessor)
      []
      callerContext
      (summary (ReplaceCallee replaceInterface (Just replaceState)))
  let finalState = checkedInvocationFinalCallableState checked
  assert
    (lookupCallableOccurrence replacePredecessorKey finalState == Nothing)
    "ReplaceCallee lifecycle witness retained predecessor"
  assert
    (lookupCallableOccurrence replaceSuccessorKey finalState == Just successor)
    "ReplaceCallee lifecycle witness did not install exact successor"

missingLifecycleBindingRejects :: Either String ()
missingLifecycleBindingRejects = do
  initialOccurrence <- consumeOccurrence
  case checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
      Map.empty
      (singletonCallableResourceState initialOccurrence)
      []
      callerContext
      (summary ConsumeCallee) of
    Left (SurfaceInvocationLifecycleRejected
      (SurfaceCallableLifecycleBindingDomainMismatch expected actual))
      | expected == Set.singleton (invocationSpan, workerKey)
          && Set.null actual -> Right ()
    Left other -> Left ("wrong missing lifecycle binding rejection: " <> show other)
    Right accepted -> Left ("missing lifecycle binding accepted: " <> show accepted)

concreteTransitionSubstitutionRejects :: Either String ()
concreteTransitionSubstitutionRejects = do
  initialOccurrence <- preserveOccurrence
  case checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
      (bindingMap (binding preserveKey bodyWithoutSuccessor))
      (singletonCallableResourceState initialOccurrence)
      []
      callerContext
      (summary ConsumeCallee) of
    Left (SurfaceInvocationLifecycleRejected
      (SurfaceCallableLifecycleTransitionMismatch identity ConsumeCallee PreserveCallee))
      | identity == (invocationSpan, workerKey) -> Right ()
    Left other -> Left ("wrong lifecycle transition substitution rejection: " <> show other)
    Right accepted -> Left ("concrete lifecycle transition substitution accepted: " <> show accepted)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
