module Phil.Compiler.CallableInvocationContext
  ( SurfaceCallableCallerContext (..)
  , CheckedSurfaceCallableInvocationContext (..)
  , CheckedSurfaceCallableInvocationLifecycleContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummary
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
  , checkSurfaceComponentWithInvocationContext
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Compiler.CallableInvocationLifecycle
  ( SurfaceCallableInvocationLifecycleBinding
  , SurfaceCallableInvocationLifecycleError
  , SurfaceCallableInvocationLifecycleWitness
  , applySurfaceCallableInvocationLifecycles
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  )
import Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation
  , SurfaceCallableOutcomeContinuationError
  , composeSurfaceCallableOutcomeContinuations
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeControl (..)
  )
import Phil.Compiler.CallableSurfaceSemantics
  ( checkSurfaceComponentWithCallableSemantics
  )
import Phil.Core.Callable
  ( CalleeTransition (..)
  , CallableCheckError
  , CallableResourceState
  , CheckedCallableEffects
  , checkCallableEffectBound
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement
  , CallableFailure (..)
  , CallableRefinementSurface (..)
  )
import Phil.Core.CallableSemanticContract
  ( SourceCallableSemanticContract
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Check
  ( SurfaceCheckError
  , SurfaceEnvironment
  )
import Phil.Surface.Syntax
  ( Component
  , Located
  , SourceSpan
  )

data SurfaceCallableCallerContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority :: Set CallableAuthorityRequirement
  , surfaceCallerPublicContract :: CallableRefinementSurface
  }
  deriving (Eq, Show)

data CheckedSurfaceCallableInvocationContext = CheckedSurfaceCallableInvocationContext
  { checkedInvocationSemanticSummary :: SurfaceCallableSemanticSummary
  , checkedInvocationEffectBound :: CheckedCallableEffects
  , checkedInvocationOutcomeContinuations :: [SurfaceCallableOutcomeContinuation]
  }
  deriving (Eq, Show)

-- | CALL-019 invocation context plus exact executable callee-lifecycle evidence.
-- The legacy/branch-aware context remains available unchanged for callers that
-- are only competent to admit PreserveCallee. Consume/Replace admission must
-- pass through this carrier so the certified Core lifecycle transition is
-- applied to concrete callable occurrence state in exact source order.
data CheckedSurfaceCallableInvocationLifecycleContext =
  CheckedSurfaceCallableInvocationLifecycleContext
    { checkedLifecycleInvocationContext :: CheckedSurfaceCallableInvocationContext
    , checkedInvocationLifecycleWitnesses :: [SurfaceCallableInvocationLifecycleWitness]
    , checkedInvocationFinalCallableState :: CallableResourceState
    }
  deriving (Eq, Show)

data SurfaceCallableInvocationContextError
  = SurfaceInvocationRejected SurfaceCheckError
  | SurfaceInvocationMissingCallerAuthority
      (Set CallableAuthorityRequirement)
  | SurfaceInvocationEffectRejected CallableCheckError
  | SurfaceInvocationFailureSetExceeded
      (Set CallableFailure)
  | SurfaceInvocationDirectCalleeTransitionUnsupported
      SourceSpan
      CalleeTransition
  | SurfaceInvocationOutcomeShapeUnsupported
      SourceSpan
      [CallableOutcomeClass]
  | SurfaceInvocationOutcomeTransitionMismatch
      SourceSpan
      CalleeTransition
      CalleeTransition
  | SurfaceInvocationOutcomeWitnessMissing
      SourceSpan
      DeclarationKey
  | SurfaceInvocationOutcomeWitnessDuplicateClass
      SourceSpan
      CallableOutcomeClass
  | SurfaceInvocationOutcomeWitnessDomainMismatch
      SourceSpan
      (Set CallableOutcomeClass)
      (Set CallableOutcomeClass)
  | SurfaceInvocationOutcomeWitnessContractMismatch
      SourceSpan
      CallableOutcomeClass
  | SurfaceInvocationOutcomeWitnessControlMismatch
      SourceSpan
      CallableOutcomeClass
  | SurfaceInvocationOutcomeWitnessUnowned
      SourceSpan
      DeclarationKey
  | SurfaceInvocationOutcomeContinuationRejected
      SurfaceCallableOutcomeContinuationError
  | SurfaceInvocationLifecycleRejected
      SurfaceCallableInvocationLifecycleError
  deriving (Eq, Show)

-- | Check one already-derived CALL-019 semantic summary against the enclosing
-- caller context. Keeping this entry point separate lets competent upstream
-- bridges establish authority possession before invoking the same effect,
-- failure, lifecycle, and outcome checks, without re-running source evaluation.
--
-- This legacy entry point intentionally remains fail-closed for branch-sensitive
-- direct calls. Callers that have established exact source-arm correlation use
-- 'checkSurfaceCallableInvocationSummaryWithOutcomeBranches' instead.
checkSurfaceCallableInvocationSummary
  :: SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceCallableInvocationSummary callerContext summary = do
  mapM_ checkDirectAccount (surfaceCallableSemanticAccounts summary)
  checkCallerContext [] callerContext summary

-- | Branch-aware CALL-019 context admission. Multi-outcome direct invocations
-- are accepted only when compiler-side arm witnesses cover the exact semantic
-- branch domain for that invocation occurrence and retain each complete outcome
-- contract unchanged. No branch buckets are unioned or reconstructed here.
--
-- After admission, the exact witnesses are projected into branch-local outcome
-- continuation records. This makes state, postconditions, residual obligations,
-- assumptions, effects, discharged facts, lifecycle, and caller-control
-- disposition available to successor compiler passes without teaching Surface
-- about CALL semantic types or flattening sibling outcomes together.
--
-- This entry point intentionally retains the old PreserveCallee-only lifecycle
-- boundary. Consume/Replace callers must use the lifecycle-aware entry point
-- below and provide exact concrete occurrence/body witnesses.
checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  :: [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceCallableInvocationSummaryWithOutcomeBranches witnesses callerContext summary = do
  let accounts = surfaceCallableSemanticAccounts summary
  mapM_ (checkWitnessOwned accounts) witnesses
  mapM_ (checkDirectAccountWithOutcomeBranches witnesses) accounts
  continuations <- mapLeft SurfaceInvocationOutcomeContinuationRejected
    (composeSurfaceCallableOutcomeContinuations witnesses)
  checkCallerContext continuations callerContext summary

-- | Lifecycle-aware branch admission. Outcome/control/refinement checks are the
-- same as the branch-aware path, but the coarse PreserveCallee guard is replaced
-- by exact occurrence-state evidence. The lifecycle bridge independently checks
-- binding domain/identity, concrete predecessor availability, transition
-- equality and the certified Preserve/Consume/Replace state mutation.
--
-- Supplying no outcome-arm witnesses remains valid for a single ordinary success
-- outcome, matching the branch-aware path. Branch-sensitive invocations still
-- require their exact arm witness domain; fatal witnesses are admitted only when
-- their exact source control is the declared-fatal control class.
checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
  :: Map (SourceSpan, DeclarationKey) SurfaceCallableInvocationLifecycleBinding
  -> CallableResourceState
  -> [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError
       CheckedSurfaceCallableInvocationLifecycleContext
checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle
    lifecycleBindings initialCallableState witnesses callerContext summary = do
  let accounts = surfaceCallableSemanticAccounts summary
  mapM_ (checkWitnessOwned accounts) witnesses
  mapM_ (checkDirectAccountWithOutcomeBranchesAfterLifecycle witnesses) accounts
  continuations <- mapLeft SurfaceInvocationOutcomeContinuationRejected
    (composeSurfaceCallableOutcomeContinuations witnesses)
  checkedContext <- checkCallerContext continuations callerContext summary
  (lifecycleWitnesses, finalCallableState) <-
    mapLeft SurfaceInvocationLifecycleRejected $
      applySurfaceCallableInvocationLifecycles
        lifecycleBindings
        accounts
        initialCallableState
  pure CheckedSurfaceCallableInvocationLifecycleContext
    { checkedLifecycleInvocationContext = checkedContext
    , checkedInvocationLifecycleWitnesses = lifecycleWitnesses
    , checkedInvocationFinalCallableState = finalCallableState
    }

checkCallerContext
  :: [SurfaceCallableOutcomeContinuation]
  -> SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkCallerContext continuations callerContext summary = do
  let missingAuthority = Set.difference
        (surfaceRequiredCallerAuthority summary)
        (surfaceCallerAvailableAuthority callerContext)
  if Set.null missingAuthority
    then pure ()
    else Left (SurfaceInvocationMissingCallerAuthority missingAuthority)
  checkedEffects <- mapLeft SurfaceInvocationEffectRejected $
    checkCallableEffectBound
      (callableRefinementContract (surfaceCallerPublicContract callerContext))
      (surfaceReachableCallableEffects summary)
  let excessFailures = Set.difference
        (surfaceReachableCallableFailures summary)
        (callableRefinementFailures (surfaceCallerPublicContract callerContext))
  if Set.null excessFailures
    then pure ()
    else Left (SurfaceInvocationFailureSetExceeded excessFailures)
  pure CheckedSurfaceCallableInvocationContext
    { checkedInvocationSemanticSummary = summary
    , checkedInvocationEffectBound = checkedEffects
    , checkedInvocationOutcomeContinuations = continuations
    }

checkSurfaceComponentWithInvocationContext
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceCallableCallerContext
  -> SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceComponentWithInvocationContext contracts callerContext environment component = do
  checked <- mapLeft SurfaceInvocationRejected $
    checkSurfaceComponentWithCallableSemantics contracts environment component
  checkSurfaceCallableInvocationSummary
    callerContext
    (summarizeSurfaceCallableSemantics checked)

checkDirectAccount
  :: SurfaceCallableInvocationSemanticAccount
  -> Either SurfaceCallableInvocationContextError ()
checkDirectAccount account = do
  checkDirectCalleeTransition account
  case surfaceSemanticInvocationOutcomes account of
    [outcome]
      | callableOutcomeClass outcome == CallableSuccessOutcome ->
          checkOutcomeTransition account outcome
    outcomes -> Left
      (SurfaceInvocationOutcomeShapeUnsupported
        (surfaceSemanticInvocationSpan account)
        (map callableOutcomeClass outcomes))

checkDirectAccountWithOutcomeBranches
  :: [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableInvocationSemanticAccount
  -> Either SurfaceCallableInvocationContextError ()
checkDirectAccountWithOutcomeBranches witnesses account = do
  checkDirectCalleeTransition account
  checkDirectAccountWithOutcomeBranchesAfterLifecycle witnesses account

-- | Branch/outcome validation after a competent lifecycle layer has taken
-- responsibility for the callee transition. This deliberately omits only the
-- PreserveCallee guard; exact outcome-transition equality is still required.
checkDirectAccountWithOutcomeBranchesAfterLifecycle
  :: [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableInvocationSemanticAccount
  -> Either SurfaceCallableInvocationContextError ()
checkDirectAccountWithOutcomeBranchesAfterLifecycle witnesses account = do
  let matching = filter (witnessBelongsTo account) witnesses
      outcomes = surfaceSemanticInvocationOutcomes account
  case (outcomes, matching) of
    ([outcome], [])
      | callableOutcomeClass outcome == CallableSuccessOutcome ->
          checkOutcomeTransition account outcome
    (_, []) -> Left
      (SurfaceInvocationOutcomeWitnessMissing
        (surfaceSemanticInvocationSpan account)
        (surfaceSemanticInvocationDeclarationKey account))
    _ -> checkExactOutcomeWitnesses account outcomes matching

checkExactOutcomeWitnesses
  :: SurfaceCallableInvocationSemanticAccount
  -> [CallableOutcomeContract]
  -> [SurfaceCallableOutcomeArmSemanticWitness]
  -> Either SurfaceCallableInvocationContextError ()
checkExactOutcomeWitnesses account outcomes witnesses = do
  actualByClass <- normalizeOutcomeWitnesses
    (surfaceSemanticInvocationSpan account)
    witnesses
  let expectedClasses = Set.fromList (map callableOutcomeClass outcomes)
      actualClasses = Map.keysSet actualByClass
  if expectedClasses == actualClasses
    then pure ()
    else Left
      (SurfaceInvocationOutcomeWitnessDomainMismatch
        (surfaceSemanticInvocationSpan account)
        expectedClasses
        actualClasses)
  mapM_ (checkOne actualByClass) outcomes
  where
    checkOne actualByClass expected = do
      let outcomeClass = callableOutcomeClass expected
      witness <- case Map.lookup outcomeClass actualByClass of
        Just value -> Right value
        Nothing -> Left
          (SurfaceInvocationOutcomeWitnessDomainMismatch
            (surfaceSemanticInvocationSpan account)
            (Set.fromList (map callableOutcomeClass outcomes))
            (Map.keysSet actualByClass))
      if surfaceOutcomeArmContract witness == expected
        then pure ()
        else Left
          (SurfaceInvocationOutcomeWitnessContractMismatch
            (surfaceSemanticInvocationSpan account)
            outcomeClass)
      if witnessControlMatches witness
        then pure ()
        else Left
          (SurfaceInvocationOutcomeWitnessControlMismatch
            (surfaceSemanticInvocationSpan account)
            outcomeClass)
      checkOutcomeTransition account expected

normalizeOutcomeWitnesses
  :: SourceSpan
  -> [SurfaceCallableOutcomeArmSemanticWitness]
  -> Either SurfaceCallableInvocationContextError
       (Map CallableOutcomeClass SurfaceCallableOutcomeArmSemanticWitness)
normalizeOutcomeWitnesses invocationSpan = foldl addWitness (Right Map.empty)
  where
    addWitness accumulated witness = do
      normalized <- accumulated
      let outcomeClass = callableOutcomeClass (surfaceOutcomeArmContract witness)
      if Map.member outcomeClass normalized
        then Left
          (SurfaceInvocationOutcomeWitnessDuplicateClass invocationSpan outcomeClass)
        else Right (Map.insert outcomeClass witness normalized)

witnessControlMatches :: SurfaceCallableOutcomeArmSemanticWitness -> Bool
witnessControlMatches witness =
  case ( callableOutcomeClass (surfaceOutcomeArmContract witness)
       , surfaceOutcomeArmControl witness
       ) of
    (CallableSuccessOutcome, SurfaceCallableOutcomeContinues) -> True
    ( CallableNonSuccessOutcome (CallableTypedNegative _)
      , SurfaceCallableOutcomeContinues
      ) -> True
    ( CallableNonSuccessOutcome (CallableDeclaredTerminal _)
      , SurfaceCallableOutcomeDeclaredTerminal
      ) -> True
    ( CallableNonSuccessOutcome (CallableFatal _)
      , SurfaceCallableOutcomeFatalTerminal
      ) -> True
    _ -> False

checkWitnessOwned
  :: [SurfaceCallableInvocationSemanticAccount]
  -> SurfaceCallableOutcomeArmSemanticWitness
  -> Either SurfaceCallableInvocationContextError ()
checkWitnessOwned accounts witness
  | any (`witnessBelongsTo` witness) accounts = Right ()
  | otherwise = Left
      (SurfaceInvocationOutcomeWitnessUnowned
        (surfaceOutcomeArmInvocationSpan witness)
        (surfaceOutcomeArmDeclarationKey witness))

witnessBelongsTo
  :: SurfaceCallableInvocationSemanticAccount
  -> SurfaceCallableOutcomeArmSemanticWitness
  -> Bool
witnessBelongsTo account witness =
  surfaceSemanticInvocationSpan account == surfaceOutcomeArmInvocationSpan witness
    && surfaceSemanticInvocationDeclarationKey account
      == surfaceOutcomeArmDeclarationKey witness

checkDirectCalleeTransition
  :: SurfaceCallableInvocationSemanticAccount
  -> Either SurfaceCallableInvocationContextError ()
checkDirectCalleeTransition account =
  case surfaceSemanticInvocationCalleeTransition account of
    PreserveCallee -> Right ()
    transition -> Left
      (SurfaceInvocationDirectCalleeTransitionUnsupported
        (surfaceSemanticInvocationSpan account)
        transition)

checkOutcomeTransition
  :: SurfaceCallableInvocationSemanticAccount
  -> CallableOutcomeContract
  -> Either SurfaceCallableInvocationContextError ()
checkOutcomeTransition account outcome =
  if callableOutcomeCalleeTransition outcome
      == surfaceSemanticInvocationCalleeTransition account
    then Right ()
    else Left
      (SurfaceInvocationOutcomeTransitionMismatch
        (surfaceSemanticInvocationSpan account)
        (surfaceSemanticInvocationCalleeTransition account)
        (callableOutcomeCalleeTransition outcome))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
