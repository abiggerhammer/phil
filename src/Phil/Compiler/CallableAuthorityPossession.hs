module Phil.Compiler.CallableAuthorityPossession
  ( CallableAuthorityPossessionBinding (..)
  , CheckedCallableAuthorityPossession (..)
  , CheckedSurfaceCallableAuthorityContext (..)
  , CallableAuthorityPossessionError (..)
  , SurfaceCallableAuthorityContextError (..)
  , derivePossessedCallableAuthority
  , checkSurfaceComponentWithAuthorityPossession
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Compiler.CallableInvocationContext
  ( CheckedSurfaceCallableInvocationContext
  , SurfaceCallableCallerContext (..)
  , SurfaceCallableInvocationContextError
  , checkSurfaceCallableInvocationSummary
  )
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  )
import Phil.Compiler.CallableSurfaceSemantics
  ( checkSurfaceComponentWithCallableSemantics
  )
import Phil.Core.Authority
  ( AuthorityCheckError
  , AuthorityExerciseSource (..)
  , AuthorityRequirement
  , AuthorityState
  , CapabilityOccurrenceKey
  , CheckedAuthorityExercise
  , checkAuthorityExercise
  )
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement
  , CallableRefinementSurface
  )
import Phil.Core.CallableSemanticContract (SourceCallableSemanticContract)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Check (SurfaceCheckError, SurfaceEnvironment)
import Phil.Surface.Syntax (Component, Located)

data CallableAuthorityPossessionBinding = CallableAuthorityPossessionBinding
  { callableAuthorityBindingRequirement :: CallableAuthorityRequirement
  , callableAuthorityBindingExactRequirement :: AuthorityRequirement
  , callableAuthorityBindingCapabilityOccurrence :: CapabilityOccurrenceKey
  }
  deriving (Eq, Ord, Show)

data CheckedCallableAuthorityPossession = CheckedCallableAuthorityPossession
  { checkedCallableAuthorityRequirement :: CallableAuthorityRequirement
  , checkedCallableAuthorityExercise :: CheckedAuthorityExercise
  }
  deriving (Eq, Ord, Show)

data CheckedSurfaceCallableAuthorityContext = CheckedSurfaceCallableAuthorityContext
  { checkedSurfaceCallableAuthorityPossessions :: [CheckedCallableAuthorityPossession]
  , checkedSurfaceCallableInvocationContext :: CheckedSurfaceCallableInvocationContext
  }
  deriving (Eq, Show)

data CallableAuthorityPossessionError
  = CallableAuthorityBindingMissing CallableAuthorityRequirement
  | CallableAuthorityBindingKeyMismatch
      CallableAuthorityRequirement
      CallableAuthorityRequirement
  | CallableAuthorityExerciseRejected
      CallableAuthorityRequirement
      AuthorityCheckError
  deriving (Eq, Ord, Show)

data SurfaceCallableAuthorityContextError
  = SurfaceCallableAuthoritySourceRejected SurfaceCheckError
  | SurfaceCallableAuthorityPossessionRejected CallableAuthorityPossessionError
  | SurfaceCallableAuthorityInvocationContextRejected
      SurfaceCallableInvocationContextError
  deriving (Eq, Show)

-- | Establish exactly the requested callable authority identities from exact
-- Core authority possession. The callable label is opaque: no spelling parser,
-- provider lookup, effect permission, runtime handle, or ambient registry entry
-- can synthesize a successful result.
derivePossessedCallableAuthority
  :: Set CallableAuthorityRequirement
  -> Map CallableAuthorityRequirement CallableAuthorityPossessionBinding
  -> AuthorityState
  -> Either CallableAuthorityPossessionError
       (Set CallableAuthorityRequirement, [CheckedCallableAuthorityPossession])
derivePossessedCallableAuthority required bindings authorityState = do
  checked <- mapM checkOne (Set.toAscList required)
  pure (Set.fromList (map checkedCallableAuthorityRequirement checked), checked)
  where
    checkOne requirement = do
      binding <- maybe
        (Left (CallableAuthorityBindingMissing requirement))
        Right
        (Map.lookup requirement bindings)
      if callableAuthorityBindingRequirement binding == requirement
        then pure ()
        else Left
          (CallableAuthorityBindingKeyMismatch
            requirement
            (callableAuthorityBindingRequirement binding))
      exercise <- mapLeft (CallableAuthorityExerciseRejected requirement) $
        checkAuthorityExercise
          (callableAuthorityBindingExactRequirement binding)
          (PossessedCapability
            (callableAuthorityBindingCapabilityOccurrence binding))
          authorityState
      pure CheckedCallableAuthorityPossession
        { checkedCallableAuthorityRequirement = requirement
        , checkedCallableAuthorityExercise = exercise
        }

-- | Full CALL-019 authority path for ordinary source invocation. Source semantics
-- are checked once, the exact required callable-authority set is projected from
-- that result, each requirement is proven by the certified Core possession
-- checker, and only that possession-derived set is supplied to the caller-context
-- effect/failure/lifecycle checker.
checkSurfaceComponentWithAuthorityPossession
  :: Map DeclarationKey SourceCallableSemanticContract
  -> Map CallableAuthorityRequirement CallableAuthorityPossessionBinding
  -> AuthorityState
  -> CallableRefinementSurface
  -> SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCallableAuthorityContextError CheckedSurfaceCallableAuthorityContext
checkSurfaceComponentWithAuthorityPossession
    contracts bindings authorityState callerPublicContract environment component = do
  checkedSurface <- mapLeft SurfaceCallableAuthoritySourceRejected $
    checkSurfaceComponentWithCallableSemantics contracts environment component
  let summary = summarizeSurfaceCallableSemantics checkedSurface
  (availableAuthority, checkedPossessions) <-
    mapLeft SurfaceCallableAuthorityPossessionRejected $
      derivePossessedCallableAuthority
        (surfaceRequiredCallerAuthority summary)
        bindings
        authorityState
  checkedContext <- mapLeft SurfaceCallableAuthorityInvocationContextRejected $
    checkSurfaceCallableInvocationSummary
      SurfaceCallableCallerContext
        { surfaceCallerAvailableAuthority = availableAuthority
        , surfaceCallerPublicContract = callerPublicContract
        }
      summary
  pure CheckedSurfaceCallableAuthorityContext
    { checkedSurfaceCallableAuthorityPossessions = checkedPossessions
    , checkedSurfaceCallableInvocationContext = checkedContext
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
