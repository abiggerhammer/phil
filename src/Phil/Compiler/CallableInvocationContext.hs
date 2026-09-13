module Phil.Compiler.CallableInvocationContext
  ( SurfaceCallableCallerContext (..)
  , CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummary
  , checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  , checkSurfaceComponentWithInvocationContext
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  )
import Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
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
  checkCallerContext callerContext summary

-- | Branch-aware CALL-019 context admission. Multi-outcome direct invocations
-- are accepted only when compiler-side arm witnesses cover the exact semantic
-- branch domain for that invocation occurrence and retain each complete outcome
-- contract unchanged. No branch buckets are unioned or reconstructed here.
--
-- Direct named lifecycle remains fail-closed except for PreserveCallee, and
-- fatal outcomes remain inadmissible because Surface still has no exact fatal
-- control representation. The witness list may cover multiple invocation
-- occurrences in one component; every witness must belong to one exact account.
checkSurfaceCallableInvocationSummaryWithOutcomeBranches
  :: [SurfaceCallableOutcomeArmSemanticWitness]
  -> SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceCallableInvocationSummaryWithOutcomeBranches witnesses callerContext summary = do
  let accounts = surfaceCallableSemanticAccounts summary
  mapM_ (checkWitnessOwned accounts) witnesses
  mapM_ (checkDirectAccountWithOutcomeBranches witnesses) accounts
  checkCallerContext callerContext summary

checkCallerContext
  :: SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkCallerContext callerContext summary = do
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
    -- Fatal outcomes cannot be produced by the installed neutral Surface
    -- dispatch yet; a hand-constructed fatal witness must not bypass that seam.
    (CallableNonSuccessOutcome (CallableFatal _), _) -> False
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
