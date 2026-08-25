{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableRefinement
  ( CallableMachineShape (..)
  , CallableAuthorityRequirement (..)
  , CallableFailure (..)
  , CallableRefinementSurface (..)
  , CheckedCallableRefinement (..)
  , CallableRefinementError (..)
  , checkCallableRefinement
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable
  ( CallableContract (..)
  , CalleeTransition
  , SemanticEffect
  )
import Phil.Core.Syntax (Outcome)

-- | Opaque checked machine-facing parameter/result shape. Equality here is only
-- one necessary condition for higher-order substitution; it is intentionally
-- insufficient to establish semantic callable refinement.
newtype CallableMachineShape = CallableMachineShape
  { unCallableMachineShape :: Text
  }
  deriving (Eq, Ord, Show)

-- | Stable semantic authority requirement visible at the callable boundary.
-- This is deliberately not a provider name, runtime handle, or implementation
-- symbol: ADR-014 requires authority to follow checked semantic value flow.
newtype CallableAuthorityRequirement = CallableAuthorityRequirement
  { unCallableAuthorityRequirement :: Text
  }
  deriving (Eq, Ord, Show)

-- | Caller-visible modeled non-success behavior for the bounded CALL-012 slice.
-- Success is implicit; typed-negative, declared-terminal, and fatal behavior
-- remain distinct because introducing a fatal path is not ordinary subtyping.
data CallableFailure
  = CallableTypedNegative Outcome
  | CallableDeclaredTerminal Outcome
  | CallableFatal Text
  deriving (Eq, Ord, Show)

-- | Checker-facing public callable facts needed for the first higher-order
-- refinement slice. Later tranches may add preconditions, result guarantees,
-- assumptions, costs, and richer parameter/resource telescopes without changing
-- the non-widening direction fixed here.
data CallableRefinementSurface = CallableRefinementSurface
  { callableRefinementMachineShape :: CallableMachineShape
  , callableRefinementContract :: CallableContract
  , callableRefinementCallerAuthority :: Set.Set CallableAuthorityRequirement
  , callableRefinementFailures :: Set.Set CallableFailure
  }
  deriving (Eq, Ord, Show)

data CheckedCallableRefinement = CheckedCallableRefinement
  { checkedCallableRefinementExpected :: CallableRefinementSurface
  , checkedCallableRefinementActual :: CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

data CallableRefinementError
  = CallableMachineShapeMismatch CallableMachineShape CallableMachineShape
  | CallableAuthorityRequirementTooStrong
      (Set.Set CallableAuthorityRequirement)
  | CallableEffectBoundTooWide
      (Set.Set SemanticEffect)
  | CallableFailureSetTooWide
      (Set.Set CallableFailure)
  | CallableCalleeTransitionIncompatible CalleeTransition CalleeTransition
  deriving (Eq, Ord, Show)

-- | Check whether an actual callable may be supplied where an expected callable
-- contract is required. The first Phase 1 relation is deliberately asymmetric:
-- the actual may require less authority, permit fewer effects/failures, and use
-- the same callee lifecycle, but it may not demand or expose anything wider.
--
-- Exact machine-shape equality is checked first but is never sufficient by
-- itself. Callee transitions are conservative/exact in v1; any nontrivial
-- preserving/consuming/replacing adaptation must become an explicit checked
-- refinement rather than an implicit coercion.
checkCallableRefinement
  :: CallableRefinementSurface
  -> CallableRefinementSurface
  -> Either CallableRefinementError CheckedCallableRefinement
checkCallableRefinement expected actual
  | actualShape /= expectedShape =
      Left (CallableMachineShapeMismatch expectedShape actualShape)
  | not (Set.null excessAuthority) =
      Left (CallableAuthorityRequirementTooStrong excessAuthority)
  | not (Set.null excessEffects) =
      Left (CallableEffectBoundTooWide excessEffects)
  | not (Set.null excessFailures) =
      Left (CallableFailureSetTooWide excessFailures)
  | actualTransition /= expectedTransition =
      Left (CallableCalleeTransitionIncompatible expectedTransition actualTransition)
  | otherwise = Right CheckedCallableRefinement
      { checkedCallableRefinementExpected = expected
      , checkedCallableRefinementActual = actual
      }
  where
    expectedShape = callableRefinementMachineShape expected
    actualShape = callableRefinementMachineShape actual
    expectedContract = callableRefinementContract expected
    actualContract = callableRefinementContract actual
    excessAuthority = Set.difference
      (callableRefinementCallerAuthority actual)
      (callableRefinementCallerAuthority expected)
    excessEffects = Set.difference
      (callableContractEffectBound actualContract)
      (callableContractEffectBound expectedContract)
    excessFailures = Set.difference
      (callableRefinementFailures actual)
      (callableRefinementFailures expected)
    expectedTransition = callableContractCalleeTransition expectedContract
    actualTransition = callableContractCalleeTransition actualContract
