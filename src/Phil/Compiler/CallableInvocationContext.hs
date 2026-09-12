module Phil.Compiler.CallableInvocationContext
  ( SurfaceCallableCallerContext (..)
  , CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableInvocationContextError (..)
  , checkSurfaceCallableInvocationSummary
  , checkSurfaceComponentWithInvocationContext
  ) where

import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
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
  , CallableFailure
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
  deriving (Eq, Show)

-- | Check one already-derived CALL-019 semantic summary against the enclosing
-- caller context. Keeping this entry point separate lets competent upstream
-- bridges establish authority possession before invoking the same effect,
-- failure, lifecycle, and outcome checks, without re-running source evaluation.
checkSurfaceCallableInvocationSummary
  :: SurfaceCallableCallerContext
  -> SurfaceCallableSemanticSummary
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceCallableInvocationSummary callerContext summary = do
  mapM_ checkDirectAccount (surfaceCallableSemanticAccounts summary)
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
  case surfaceSemanticInvocationCalleeTransition account of
    PreserveCallee -> pure ()
    transition -> Left
      (SurfaceInvocationDirectCalleeTransitionUnsupported
        (surfaceSemanticInvocationSpan account)
        transition)
  case surfaceSemanticInvocationOutcomes account of
    [outcome]
      | callableOutcomeClass outcome == CallableSuccessOutcome ->
          if callableOutcomeCalleeTransition outcome
              == surfaceSemanticInvocationCalleeTransition account
            then pure ()
            else Left
              (SurfaceInvocationOutcomeTransitionMismatch
                (surfaceSemanticInvocationSpan account)
                (surfaceSemanticInvocationCalleeTransition account)
                (callableOutcomeCalleeTransition outcome))
    outcomes -> Left
      (SurfaceInvocationOutcomeShapeUnsupported
        (surfaceSemanticInvocationSpan account)
        (map callableOutcomeClass outcomes))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
