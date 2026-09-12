module Phil.Compiler.CallableInvocationContext
  ( SurfaceCallableCallerContext (..)
  , CheckedSurfaceCallableInvocationContext (..)
  , SurfaceCallableInvocationContextError (..)
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

-- | Caller facts supplied by competent layers around ordinary source invocation.
-- `surfaceCallerAvailableAuthority` is intentionally already normalized to the
-- callable-level authority identity. This module does not manufacture possession
-- from names: a later bridge from `Phil.Core.Authority` must establish that set
-- from actually possessed capability/provider values.
data SurfaceCallableCallerContext = SurfaceCallableCallerContext
  { surfaceCallerAvailableAuthority :: Set CallableAuthorityRequirement
  , surfaceCallerPublicContract :: CallableRefinementSurface
  }
  deriving (Eq, Show)

-- | Successful composition of accepted source invocations with the enclosing
-- caller contract. The complete semantic summary remains available, while the
-- effect-bound witness proves that all reachable invocation effects fit inside
-- the caller's stabilized public may-effect bound.
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

-- | Check ordinary source invocation through the complete CALL-019 composition
-- path currently representable by the surface evaluator.
--
-- The ordinary surface checker still owns syntax, parameter/result type shape,
-- and restricted argument transfer. CALL-019 then binds every explicit invoke to
-- an exact semantic contract and projects its caller-visible account. This layer
-- additionally checks that:
--
-- * caller-required authority is available from an explicitly supplied
--   possession-derived authority set;
-- * reachable invocation effects fit the enclosing callable's public bound via
--   the existing CALL effect checker;
-- * modeled callee failures fit the enclosing callable's public failure set; and
-- * the current direct named-invoke execution shape is used only when its outcome
--   and callee lifecycle can be represented faithfully.
--
-- Branch-sensitive invocation and consuming/replacing first-class callee owners
-- are rejected here rather than silently flattened. Later CALL-019 slices can
-- replace those rejections with explicit branch/resource-state composition.
checkSurfaceComponentWithInvocationContext
  :: Map DeclarationKey SourceCallableSemanticContract
  -> SurfaceCallableCallerContext
  -> SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCallableInvocationContextError CheckedSurfaceCallableInvocationContext
checkSurfaceComponentWithInvocationContext contracts callerContext environment component = do
  checked <- mapLeft SurfaceInvocationRejected $
    checkSurfaceComponentWithCallableSemantics contracts environment component
  let summary = summarizeSurfaceCallableSemantics checked
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
