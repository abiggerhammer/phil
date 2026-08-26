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

import qualified CallableRefinementKernel as Kernel
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
  | CallableRefinementRepresentationBridgeMismatch Text
  deriving (Eq, Ord, Show)

-- | Check whether an actual callable may be supplied where an expected callable
-- contract is required. Acceptance is decided by the Rocq-extracted CALL-012
-- kernel. Haskell constructs the finite projection and diagnostic payloads, but
-- it is deliberately unable to turn a kernel rejection into acceptance.
--
-- Set projections use a finite ascending domain for the union of actual and
-- expected elements. The incidence encoder itself is extracted from the proved
-- bridge model. Runtime round-trip checks fail closed if the concrete Data.Set
-- view does not reconstruct the exact source sets for this comparison.
checkCallableRefinement
  :: CallableRefinementSurface
  -> CallableRefinementSurface
  -> Either CallableRefinementError CheckedCallableRefinement
checkCallableRefinement expected actual = do
  (actualAuthorityBits, expectedAuthorityBits) <-
    incidencePair
      "caller-authority"
      (callableRefinementCallerAuthority actual)
      (callableRefinementCallerAuthority expected)
  (actualEffectBits, expectedEffectBits) <-
    incidencePair
      "effect-bound"
      (callableContractEffectBound actualContract)
      (callableContractEffectBound expectedContract)
  (actualFailureBits, expectedFailureBits) <-
    incidencePair
      "failure-set"
      (callableRefinementFailures actual)
      (callableRefinementFailures expected)
  let projection = Kernel.MkRefinementProjection
        (actualShape == expectedShape)
        actualAuthorityBits
        expectedAuthorityBits
        actualEffectBits
        expectedEffectBits
        actualFailureBits
        expectedFailureBits
        (actualTransition == expectedTransition)
  case Kernel.decideCallableRefinement projection of
    Kernel.RefinementAccepted
      | actualShape == expectedShape
          && Set.null excessAuthority
          && Set.null excessEffects
          && Set.null excessFailures
          && actualTransition == expectedTransition ->
          Right CheckedCallableRefinement
            { checkedCallableRefinementExpected = expected
            , checkedCallableRefinementActual = actual
            }
      | otherwise -> bridgeMismatch "kernel acceptance disagreed with concrete diagnostics"
    Kernel.RefinementMachineShapeMismatch
      | actualShape /= expectedShape ->
          Left (CallableMachineShapeMismatch expectedShape actualShape)
      | otherwise -> bridgeMismatch "machine-shape decision disagreed with equality projection"
    Kernel.RefinementAuthorityTooStrong
      | not (Set.null excessAuthority) ->
          Left (CallableAuthorityRequirementTooStrong excessAuthority)
      | otherwise -> bridgeMismatch "authority rejection had no concrete excess"
    Kernel.RefinementEffectsTooWide
      | not (Set.null excessEffects) ->
          Left (CallableEffectBoundTooWide excessEffects)
      | otherwise -> bridgeMismatch "effect rejection had no concrete excess"
    Kernel.RefinementFailuresTooWide
      | not (Set.null excessFailures) ->
          Left (CallableFailureSetTooWide excessFailures)
      | otherwise -> bridgeMismatch "failure rejection had no concrete excess"
    Kernel.RefinementTransitionMismatch
      | actualTransition /= expectedTransition ->
          Left (CallableCalleeTransitionIncompatible expectedTransition actualTransition)
      | otherwise -> bridgeMismatch "callee-transition decision disagreed with equality projection"
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

incidencePair
  :: Ord a
  => Text
  -> Set.Set a
  -> Set.Set a
  -> Either CallableRefinementError ([Bool], [Bool])
incidencePair label actual expected
  | domainSet /= Set.union actual expected =
      bridgeMismatch (label <> ": finite domain did not round-trip")
  | length actualBits /= length domain || length expectedBits /= length domain =
      bridgeMismatch (label <> ": extracted incidence length mismatch")
  | reconstruct actualBits /= actual =
      bridgeMismatch (label <> ": actual incidence projection did not round-trip")
  | reconstruct expectedBits /= expected =
      bridgeMismatch (label <> ": expected incidence projection did not round-trip")
  | otherwise = Right (actualBits, expectedBits)
  where
    domain = Set.toAscList (Set.union actual expected)
    domainSet = Set.fromList domain
    actualBits = Kernel.incidenceVector domain (\element -> Set.member element actual)
    expectedBits = Kernel.incidenceVector domain (\element -> Set.member element expected)
    reconstruct bits = Set.fromList
      [ element
      | (element, present) <- zip domain bits
      , present
      ]

bridgeMismatch :: Text -> Either CallableRefinementError a
bridgeMismatch = Left . CallableRefinementRepresentationBridgeMismatch
