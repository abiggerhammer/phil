{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationLifecycle
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Core.Callable
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 lifecycle witness preserves exact preserving occurrence"
        preserveWitness
    , test "CALL-019 lifecycle witness consumes one-shot occurrence"
        consumeWitness
    , test "CALL-019 lifecycle witness installs exact replacement occurrence"
        replaceWitness
    , test "CALL-019 lifecycle witness applies source occurrences sequentially"
        sequentialConsumeRejectsReuse
    , test "CALL-019 lifecycle witness rejects transition substitution"
        transitionSubstitutionRejects
    , test "CALL-019 lifecycle witness requires exact occurrence binding domain"
        bindingDomainMismatchRejects
    , test "CALL-019 lifecycle witness rejects duplicate invocation identity"
        duplicateInvocationRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

preserveSpan, consumeSpan, replaceSpan, secondConsumeSpan :: SourceSpan
preserveSpan = spanAt "call019-lifecycle" 1 10
consumeSpan = spanAt "call019-lifecycle" 2 20
replaceSpan = spanAt "call019-lifecycle" 3 30
secondConsumeSpan = spanAt "call019-lifecycle" 4 40

spanAt :: Text -> Int -> Int -> SourceSpan
spanAt file line offset = SourceSpan
  (SourcePoint file line 1 offset)
  (SourcePoint file line 2 (offset + 1))

account :: SourceSpan -> CalleeTransition -> SurfaceCallableInvocationSemanticAccount
account invocationSpan transition = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Worker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = transition
  , surfaceSemanticInvocationModeledFailures = Set.empty
  , surfaceSemanticInvocationOutcomes = [successOutcome transition]
  }

successOutcome :: CalleeTransition -> CallableOutcomeContract
successOutcome transition = CallableOutcomeContract
  { callableOutcomeClass = CallableSuccessOutcome
  , callableOutcomeState = CallableOutcomeState "state.success"
  , callableOutcomeCalleeTransition = transition
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

binding
  :: SourceSpan
  -> CallableOccurrenceKey
  -> CallableInvocationBodySummary
  -> SurfaceCallableInvocationLifecycleBinding
binding invocationSpan predecessor body = SurfaceCallableInvocationLifecycleBinding
  { surfaceLifecycleBindingInvocationSpan = invocationSpan
  , surfaceLifecycleBindingDeclarationKey = workerKey
  , surfaceLifecycleBindingPredecessor = predecessor
  , surfaceLifecycleBindingBodySummary = body
  }

preserveWitness :: Either String ()
preserveWitness = do
  let lifecycleAccount = account preserveSpan PreserveCallee
      bindings = Map.singleton
        (preserveSpan, workerKey)
        (binding preserveSpan preserveKey preserveBody)
      initial = singletonCallableResourceState preserveOccurrence
  (witnesses, finalState) <- mapLeft show $
    applySurfaceCallableInvocationLifecycles
      bindings [lifecycleAccount] [[lifecycleAccount]] initial
  assert (length witnesses == 1) "expected exactly one preserving witness"
  witness <- only witnesses
  assert
    (surfaceLifecycleWitnessTransition witness == PreserveCallee)
    "preserving witness changed transition"
  assert
    (surfaceLifecycleWitnessBefore witness == initial)
    "preserving witness lost exact before-state"
  assert
    (surfaceLifecycleWitnessAfter witness == finalState)
    "preserving witness lost exact after-state"
  assert
    (lookupCallableOccurrence preserveKey finalState == Just preserveOccurrence)
    "preserving lifecycle changed exact callable occurrence"

consumeWitness :: Either String ()
consumeWitness = do
  let lifecycleAccount = account consumeSpan ConsumeCallee
      bindings = Map.singleton
        (consumeSpan, workerKey)
        (binding consumeSpan consumeKey emptyBody)
  (_, finalState) <- mapLeft show $
    applySurfaceCallableInvocationLifecycles
      bindings
      [lifecycleAccount]
      [[lifecycleAccount]]
      (singletonCallableResourceState consumeOccurrence)
  assert
    (lookupCallableOccurrence consumeKey finalState == Nothing)
    "ConsumeCallee left predecessor available"

replaceWitness :: Either String ()
replaceWitness = do
  let transition = ReplaceCallee streamInterface (Just successorState)
      lifecycleAccount = account replaceSpan transition
      bindings = Map.singleton
        (replaceSpan, workerKey)
        (binding replaceSpan replacePredecessorKey replaceBody)
  (_, finalState) <- mapLeft show $
    applySurfaceCallableInvocationLifecycles
      bindings
      [lifecycleAccount]
      (singletonCallableResourceState replacePredecessor)
  assert
    (lookupCallableOccurrence replacePredecessorKey finalState == Nothing)
    "ReplaceCallee retained predecessor"
  assert
    (lookupCallableOccurrence replaceSuccessorKey finalState == Just replaceSuccessor)
    "ReplaceCallee did not install exact successor"

sequentialConsumeRejectsReuse :: Either String ()
sequentialConsumeRejectsReuse = do
  let first = account consumeSpan ConsumeCallee
      second = account secondConsumeSpan ConsumeCallee
      bindings = Map.fromList
        [ ((consumeSpan, workerKey), binding consumeSpan consumeKey emptyBody)
        , ((secondConsumeSpan, workerKey), binding secondConsumeSpan consumeKey emptyBody)
        ]
  case applySurfaceCallableInvocationLifecycles
      bindings
      [first, second]
      [[first, second]]
      (singletonCallableResourceState consumeOccurrence) of
    Left (SurfaceCallableLifecyclePredecessorUnavailable identity key)
      | identity == (secondConsumeSpan, workerKey)
          && key == consumeKey -> Right ()
    Left other -> Left ("wrong sequential consume rejection: " <> show other)
    Right accepted -> Left ("consumed occurrence was reused: " <> show accepted)

transitionSubstitutionRejects :: Either String ()
transitionSubstitutionRejects = do
  let lifecycleAccount = account consumeSpan PreserveCallee
      bindings = Map.singleton
        (consumeSpan, workerKey)
        (binding consumeSpan consumeKey emptyBody)
  case applySurfaceCallableInvocationLifecycles
      bindings
      [lifecycleAccount]
      [[lifecycleAccount]]
      (singletonCallableResourceState consumeOccurrence) of
    Left (SurfaceCallableLifecycleTransitionMismatch identity expected actual)
      | identity == (consumeSpan, workerKey)
          && expected == PreserveCallee
          && actual == ConsumeCallee -> Right ()
    Left other -> Left ("wrong transition-substitution rejection: " <> show other)
    Right accepted -> Left ("transition substitution accepted: " <> show accepted)

bindingDomainMismatchRejects :: Either String ()
bindingDomainMismatchRejects = do
  let lifecycleAccount = account consumeSpan ConsumeCallee
      wrong = Map.singleton
        (preserveSpan, workerKey)
        (binding preserveSpan consumeKey emptyBody)
  case applySurfaceCallableInvocationLifecycles
      wrong
      [lifecycleAccount]
      [[lifecycleAccount]]
      (singletonCallableResourceState consumeOccurrence) of
    Left (SurfaceCallableLifecycleBindingDomainMismatch expected actual)
      | expected == Set.singleton (consumeSpan, workerKey)
          && actual == Set.singleton (preserveSpan, workerKey) -> Right ()
    Left other -> Left ("wrong binding-domain rejection: " <> show other)
    Right accepted -> Left ("wrong occurrence binding accepted: " <> show accepted)

duplicateInvocationRejects :: Either String ()
duplicateInvocationRejects = do
  let lifecycleAccount = account consumeSpan ConsumeCallee
      bindings = Map.singleton
        (consumeSpan, workerKey)
        (binding consumeSpan consumeKey emptyBody)
  case applySurfaceCallableInvocationLifecycles
      bindings
      [lifecycleAccount, lifecycleAccount]
      [[lifecycleAccount, lifecycleAccount]]
      (singletonCallableResourceState consumeOccurrence) of
    Left (SurfaceCallableLifecycleDuplicateInvocation identity)
      | identity == (consumeSpan, workerKey) -> Right ()
    Left other -> Left ("wrong duplicate-invocation rejection: " <> show other)
    Right accepted -> Left ("duplicate invocation identity accepted: " <> show accepted)

preserveKey, consumeKey, replacePredecessorKey, replaceSuccessorKey
  :: CallableOccurrenceKey
preserveKey = CallableOccurrenceKey "callable.preserve.001"
consumeKey = CallableOccurrenceKey "callable.consume.001"
replacePredecessorKey = CallableOccurrenceKey "callable.replace.001"
replaceSuccessorKey = CallableOccurrenceKey "callable.replace.002"

captureKey :: CaptureOccurrenceKey
captureKey = CaptureOccurrenceKey "capture.owner.001"

preserveCaptures, emptyCaptures :: ClosureCaptureSummary
preserveCaptures = case checkClosureCaptures
    [ClosureCapture captureKey MoveCapture Linear] of
  Right value -> value
  Left errorValue -> error (show errorValue)
emptyCaptures = case checkClosureCaptures [] of
  Right value -> value
  Left errorValue -> error (show errorValue)

streamInterface :: InterfaceRevision
streamInterface = InterfaceRevision "callable.stream.v1"

successorState :: CallableStateKey
successorState = CallableStateKey "stream.S1"

preserveContract, consumeContract, replaceContract :: CallableContract
preserveContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.preserve.v1"
  , callableContractCalleeTransition = PreserveCallee
  , callableContractEffectBound = Set.empty
  }
consumeContract = CallableContract
  { callableContractInterfaceRevision = InterfaceRevision "callable.consume.v1"
  , callableContractCalleeTransition = ConsumeCallee
  , callableContractEffectBound = Set.empty
  }
replaceContract = CallableContract
  { callableContractInterfaceRevision = streamInterface
  , callableContractCalleeTransition = ReplaceCallee streamInterface (Just successorState)
  , callableContractEffectBound = Set.empty
  }

preserveOccurrence, consumeOccurrence, replacePredecessor, replaceSuccessor
  :: CallableOccurrence
preserveOccurrence = CallableOccurrence
  { callableOccurrenceKey = preserveKey
  , callableOccurrenceContract = preserveContract
  , callableOccurrenceCaptures = preserveCaptures
  , callableOccurrenceStateKey = Nothing
  }
consumeOccurrence = CallableOccurrence
  { callableOccurrenceKey = consumeKey
  , callableOccurrenceContract = consumeContract
  , callableOccurrenceCaptures = preserveCaptures
  , callableOccurrenceStateKey = Nothing
  }
replacePredecessor = CallableOccurrence
  { callableOccurrenceKey = replacePredecessorKey
  , callableOccurrenceContract = replaceContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Just (CallableStateKey "stream.S0")
  }
replaceSuccessor = CallableOccurrence
  { callableOccurrenceKey = replaceSuccessorKey
  , callableOccurrenceContract = replaceContract
  , callableOccurrenceCaptures = emptyCaptures
  , callableOccurrenceStateKey = Just successorState
  }

preserveBody, emptyBody, replaceBody :: CallableInvocationBodySummary
preserveBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.singleton captureKey
  , invocationSuccessorCallable = Nothing
  }
emptyBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Nothing
  }
replaceBody = CallableInvocationBodySummary
  { invocationRestrictedCaptureResidue = Set.empty
  , invocationSuccessorCallable = Just replaceSuccessor
  }

only :: [a] -> Either String a
only [value] = Right value
only values = Left ("expected one value, got " <> show (length values))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
