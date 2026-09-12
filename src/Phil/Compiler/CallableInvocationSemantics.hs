module Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  , SurfaceCallableSemanticSummary (..)
  , summarizeSurfaceCallableSemantics
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.CallableSurfaceSemantics
  ( SurfaceCallableInvocationWitness (..)
  , SurfaceSemanticCheckResult (..)
  )
import Phil.Core.Callable
  ( CalleeTransition
  , CallableContract (..)
  , CallableUse (..)
  , SemanticEffect
  , inferReachableCallableEffects
  )
import Phil.Core.CallableOutcome (CallableOutcomeContract)
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement
  , CallableFailure
  , CallableRefinementSurface (..)
  )
import Phil.Core.CallableSemanticContract
  ( SourceCallableSemanticContract (..)
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Syntax (SourceSpan)

-- | Exact caller-visible semantic account for one accepted ordinary source
-- invocation. This is a projection of the already-retained complete contract,
-- not a reconstructed or name-derived approximation. Keeping branch outcomes
-- intact prevents postconditions, assumptions, effects, discharged facts, and
-- residual obligations from being flattened into interchangeable sets.
data SurfaceCallableInvocationSemanticAccount = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan :: SourceSpan
  , surfaceSemanticInvocationDisplayName :: Text
  , surfaceSemanticInvocationDeclarationKey :: DeclarationKey
  , surfaceSemanticInvocationCallerAuthority :: Set CallableAuthorityRequirement
  , surfaceSemanticInvocationPublicEffectBound :: Set SemanticEffect
  , surfaceSemanticInvocationCalleeTransition :: CalleeTransition
  , surfaceSemanticInvocationModeledFailures :: Set CallableFailure
  , surfaceSemanticInvocationOutcomes :: [CallableOutcomeContract]
  }
  deriving (Eq, Ord, Show)

-- | Reachable CALL-019 summary for one already-successful surface check.
-- Invocation accounts retain source/evaluation order and multiplicity. Only
-- actual `invoke` occurrences contribute callable effects: the aggregate effect
-- footprint is deliberately derived through the existing CALL effect kernel,
-- so possessing or merely naming a callable cannot acquire its invocation
-- effects through a source-only shortcut.
data SurfaceCallableSemanticSummary = SurfaceCallableSemanticSummary
  { surfaceCallableSemanticAccounts :: [SurfaceCallableInvocationSemanticAccount]
  , surfaceReachableCallableEffects :: Set SemanticEffect
  , surfaceRequiredCallerAuthority :: Set CallableAuthorityRequirement
  , surfaceReachableCallableFailures :: Set CallableFailure
  }
  deriving (Eq, Show)

summarizeSurfaceCallableSemantics
  :: SurfaceSemanticCheckResult
  -> SurfaceCallableSemanticSummary
summarizeSurfaceCallableSemantics checked = SurfaceCallableSemanticSummary
  { surfaceCallableSemanticAccounts = accounts
  , surfaceReachableCallableEffects =
      inferReachableCallableEffects
        (map invocationUse (checkedCallableInvocations checked))
  , surfaceRequiredCallerAuthority =
      Set.unions (map surfaceSemanticInvocationCallerAuthority accounts)
  , surfaceReachableCallableFailures =
      Set.unions (map surfaceSemanticInvocationModeledFailures accounts)
  }
  where
    accounts = map semanticAccount (checkedCallableInvocations checked)

semanticAccount
  :: SurfaceCallableInvocationWitness
  -> SurfaceCallableInvocationSemanticAccount
semanticAccount witness = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = surfaceInvocationSpan witness
  , surfaceSemanticInvocationDisplayName = surfaceInvocationDisplayName witness
  , surfaceSemanticInvocationDeclarationKey = surfaceInvocationDeclarationKey witness
  , surfaceSemanticInvocationCallerAuthority =
      callableRefinementCallerAuthority refinement
  , surfaceSemanticInvocationPublicEffectBound =
      callableContractEffectBound publicContract
  , surfaceSemanticInvocationCalleeTransition =
      callableContractCalleeTransition publicContract
  , surfaceSemanticInvocationModeledFailures =
      callableRefinementFailures refinement
  , surfaceSemanticInvocationOutcomes =
      sourceCallableOutcomeContracts semanticContract
  }
  where
    semanticContract = surfaceInvocationSemanticContract witness
    refinement = sourceCallableRefinementSurface semanticContract
    publicContract = callableRefinementContract refinement

invocationUse :: SurfaceCallableInvocationWitness -> CallableUse
invocationUse witness = InvokeCallable
  (callableRefinementContract
    (sourceCallableRefinementSurface
      (surfaceInvocationSemanticContract witness)))
