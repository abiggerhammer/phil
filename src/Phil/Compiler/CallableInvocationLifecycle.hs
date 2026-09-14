module Phil.Compiler.CallableInvocationLifecycle
  ( SurfaceCallableInvocationLifecycleBinding (..)
  , SurfaceCallableInvocationLifecycleWitness (..)
  , SurfaceCallableInvocationLifecycleError (..)
  , applySurfaceCallableInvocationLifecycles
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Core.Callable
  ( CalleeTransition
  , CallableCheckError
  , CallableContract (..)
  , CallableInvocationBodySummary
  , CallableOccurrenceKey
  , CallableResourceState
  , callableOccurrenceContract
  , invokeCallableOccurrence
  , lookupCallableOccurrence
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Syntax (SourceSpan)

type InvocationIdentity = (SourceSpan, DeclarationKey)

-- | Exact compiler-owned lifecycle input for one accepted CALL-019 source
-- invocation occurrence. The key is repeated inside the value deliberately so
-- map-key substitution is detectable rather than silently trusted.
data SurfaceCallableInvocationLifecycleBinding =
  SurfaceCallableInvocationLifecycleBinding
    { surfaceLifecycleBindingInvocationSpan :: SourceSpan
    , surfaceLifecycleBindingDeclarationKey :: DeclarationKey
    , surfaceLifecycleBindingPredecessor :: CallableOccurrenceKey
    , surfaceLifecycleBindingBodySummary :: CallableInvocationBodySummary
    }
  deriving (Eq, Ord, Show)

-- | Auditable lifecycle step for one source invocation. The complete before and
-- after callable resource states are retained so sequential one-shot/replaceable
-- behavior can be checked without reconstructing state from names or contracts.
data SurfaceCallableInvocationLifecycleWitness =
  SurfaceCallableInvocationLifecycleWitness
    { surfaceLifecycleWitnessInvocationSpan :: SourceSpan
    , surfaceLifecycleWitnessDeclarationKey :: DeclarationKey
    , surfaceLifecycleWitnessPredecessor :: CallableOccurrenceKey
    , surfaceLifecycleWitnessTransition :: CalleeTransition
    , surfaceLifecycleWitnessBodySummary :: CallableInvocationBodySummary
    , surfaceLifecycleWitnessBefore :: CallableResourceState
    , surfaceLifecycleWitnessAfter :: CallableResourceState
    }
  deriving (Eq, Ord, Show)

data SurfaceCallableInvocationLifecycleError
  = SurfaceCallableLifecycleDuplicateInvocation InvocationIdentity
  | SurfaceCallableLifecycleBindingDomainMismatch
      (Set InvocationIdentity)
      (Set InvocationIdentity)
  | SurfaceCallableLifecycleBindingIdentityMismatch
      InvocationIdentity
      InvocationIdentity
  | SurfaceCallableLifecyclePredecessorUnavailable
      InvocationIdentity
      CallableOccurrenceKey
  | SurfaceCallableLifecycleTransitionMismatch
      InvocationIdentity
      CalleeTransition
      CalleeTransition
  | SurfaceCallableLifecycleRejected
      InvocationIdentity
      CallableCheckError
  deriving (Eq, Ord, Show)

-- | Apply CALL-019 callee lifecycle in exact source/evaluation order. Each
-- invocation occurrence must have exactly one competent binding. The semantic
-- account's declared callee transition must equal the predecessor occurrence's
-- concrete contract transition before the existing certified Core lifecycle
-- transition is allowed to mutate resource state.
--
-- This bridge deliberately does not yet relax Surface invocation admission. It
-- establishes the exact occurrence/state witness needed for the successor slice
-- to remove the PreserveCallee-only guard without inventing lifecycle semantics.
applySurfaceCallableInvocationLifecycles
  :: Map InvocationIdentity SurfaceCallableInvocationLifecycleBinding
  -> [SurfaceCallableInvocationSemanticAccount]
  -> CallableResourceState
  -> Either SurfaceCallableInvocationLifecycleError
       ([SurfaceCallableInvocationLifecycleWitness], CallableResourceState)
applySurfaceCallableInvocationLifecycles bindings accounts initialState = do
  expected <- exactAccountDomain accounts
  let actual = Map.keysSet bindings
  if expected == actual
    then pure ()
    else Left (SurfaceCallableLifecycleBindingDomainMismatch expected actual)
  go initialState [] accounts
  where
    go state accumulated [] = Right (reverse accumulated, state)
    go state accumulated (account : rest) = do
      let identity = accountIdentity account
      binding <- case Map.lookup identity bindings of
        Just value -> Right value
        Nothing -> Left
          (SurfaceCallableLifecycleBindingDomainMismatch
            (Set.singleton identity)
            Set.empty)
      validateBindingIdentity identity binding
      predecessor <- case lookupCallableOccurrence
          (surfaceLifecycleBindingPredecessor binding)
          state of
        Just value -> Right value
        Nothing -> Left
          (SurfaceCallableLifecyclePredecessorUnavailable
            identity
            (surfaceLifecycleBindingPredecessor binding))
      let expectedTransition = surfaceSemanticInvocationCalleeTransition account
          actualTransition = callableContractCalleeTransition
            (callableOccurrenceContract predecessor)
      if expectedTransition == actualTransition
        then pure ()
        else Left
          (SurfaceCallableLifecycleTransitionMismatch
            identity expectedTransition actualTransition)
      next <- case invokeCallableOccurrence
          (surfaceLifecycleBindingPredecessor binding)
          (surfaceLifecycleBindingBodySummary binding)
          state of
        Right value -> Right value
        Left errorValue -> Left
          (SurfaceCallableLifecycleRejected identity errorValue)
      let witness = SurfaceCallableInvocationLifecycleWitness
            { surfaceLifecycleWitnessInvocationSpan =
                surfaceSemanticInvocationSpan account
            , surfaceLifecycleWitnessDeclarationKey =
                surfaceSemanticInvocationDeclarationKey account
            , surfaceLifecycleWitnessPredecessor =
                surfaceLifecycleBindingPredecessor binding
            , surfaceLifecycleWitnessTransition = expectedTransition
            , surfaceLifecycleWitnessBodySummary =
                surfaceLifecycleBindingBodySummary binding
            , surfaceLifecycleWitnessBefore = state
            , surfaceLifecycleWitnessAfter = next
            }
      go next (witness : accumulated) rest

exactAccountDomain
  :: [SurfaceCallableInvocationSemanticAccount]
  -> Either SurfaceCallableInvocationLifecycleError (Set InvocationIdentity)
exactAccountDomain = foldl addAccount (Right Set.empty)
  where
    addAccount accumulated account = do
      seen <- accumulated
      let identity = accountIdentity account
      if Set.member identity seen
        then Left (SurfaceCallableLifecycleDuplicateInvocation identity)
        else Right (Set.insert identity seen)

validateBindingIdentity
  :: InvocationIdentity
  -> SurfaceCallableInvocationLifecycleBinding
  -> Either SurfaceCallableInvocationLifecycleError ()
validateBindingIdentity expected binding =
  let actual =
        ( surfaceLifecycleBindingInvocationSpan binding
        , surfaceLifecycleBindingDeclarationKey binding
        )
  in if expected == actual
      then Right ()
      else Left (SurfaceCallableLifecycleBindingIdentityMismatch expected actual)

accountIdentity :: SurfaceCallableInvocationSemanticAccount -> InvocationIdentity
accountIdentity account =
  ( surfaceSemanticInvocationSpan account
  , surfaceSemanticInvocationDeclarationKey account
  )
