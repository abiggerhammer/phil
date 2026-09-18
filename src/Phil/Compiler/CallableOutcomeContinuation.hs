module Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuationDisposition (..)
  , SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationError (..)
  , composeSurfaceCallableOutcomeContinuations
  ) where

import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeControl (..)
  )
import Phil.Core.Callable
  ( CalleeTransition
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax
  ( Mode
  , Outcome
  , Ty
  )
import Phil.Surface.Syntax (SourceSpan)

-- | Caller-control disposition for one exact callable outcome branch. Continuing,
-- declared-terminal, and declared-fatal outcomes remain distinct. A fatal
-- disposition terminates ordinary caller sequencing without becoming generic
-- failure or ordinary declared closure.
data SurfaceCallableOutcomeContinuationDisposition
  = SurfaceCallableOutcomeCallerContinues
  | SurfaceCallableOutcomeCallerTerminates Outcome
  | SurfaceCallableOutcomeCallerFatals Outcome
  deriving (Eq, Ord, Show)

-- | Exact branch-local semantic state made available to successor compiler
-- passes after CALL-019 branch-aware invocation admission.
--
-- The semantic buckets remain separate on purpose. Postconditions, residual
-- obligations, assumptions, effects, and discharged facts are not interchangeable
-- and are never unioned across sibling outcomes. The complete contract is also
-- retained unchanged so later resource/evidence composition can check that it is
-- consuming the same branch object rather than a reconstructed approximation.
data SurfaceCallableOutcomeContinuation = SurfaceCallableOutcomeContinuation
  { surfaceContinuationInvocationSpan :: SourceSpan
  , surfaceContinuationArmSpan :: SourceSpan
  , surfaceContinuationDeclarationKey :: DeclarationKey
  , surfaceContinuationSourceLabel :: Text
  , surfaceContinuationPayload :: [(Mode, Ty)]
  , surfaceContinuationOutcomeClass :: CallableOutcomeClass
  , surfaceContinuationDisposition :: SurfaceCallableOutcomeContinuationDisposition
  , surfaceContinuationState :: CallableOutcomeState
  , surfaceContinuationCalleeTransition :: CalleeTransition
  , surfaceContinuationPostconditions :: Set CallableOutcomeAtom
  , surfaceContinuationResidualObligations :: Set CallableOutcomeAtom
  , surfaceContinuationAssumptions :: Set CallableOutcomeAtom
  , surfaceContinuationEffects :: Set CallableOutcomeAtom
  , surfaceContinuationDischargedFacts :: Set CallableOutcomeAtom
  , surfaceContinuationContract :: CallableOutcomeContract
  }
  deriving (Eq, Ord, Show)

data SurfaceCallableOutcomeContinuationError
  = SurfaceCallableOutcomeContinuationControlMismatch
      SourceSpan
      CallableOutcomeClass
      SurfaceCallableOutcomeControl
  deriving (Eq, Ord, Show)

-- | Project exact admitted outcome witnesses into branch-local continuation
-- state. Witness/source order is preserved. Continuing success and typed-negative
-- branches become ordinary caller continuations; declared-terminal and fatal
-- outcomes retain distinct noncontinuing dispositions with exact outcome identity.
composeSurfaceCallableOutcomeContinuations
  :: [SurfaceCallableOutcomeArmSemanticWitness]
  -> Either SurfaceCallableOutcomeContinuationError
       [SurfaceCallableOutcomeContinuation]
composeSurfaceCallableOutcomeContinuations = mapM composeOne

composeOne
  :: SurfaceCallableOutcomeArmSemanticWitness
  -> Either SurfaceCallableOutcomeContinuationError SurfaceCallableOutcomeContinuation
composeOne witness =
  case (outcomeClass, surfaceOutcomeArmControl witness) of
    (CallableSuccessOutcome, SurfaceCallableOutcomeContinues) ->
      Right (continuation SurfaceCallableOutcomeCallerContinues)
    ( CallableNonSuccessOutcome (CallableTypedNegative _)
      , SurfaceCallableOutcomeContinues
      ) -> Right (continuation SurfaceCallableOutcomeCallerContinues)
    ( CallableNonSuccessOutcome (CallableDeclaredTerminal outcome)
      , SurfaceCallableOutcomeDeclaredTerminal
      ) -> Right (continuation (SurfaceCallableOutcomeCallerTerminates outcome))
    ( CallableNonSuccessOutcome (CallableFatal outcome)
      , SurfaceCallableOutcomeFatalTerminal
      ) -> Right (continuation (SurfaceCallableOutcomeCallerFatals outcome))
    (_, actualControl) ->
      Left
        (SurfaceCallableOutcomeContinuationControlMismatch
          (surfaceOutcomeArmSpan witness)
          outcomeClass
          actualControl)
  where
    contract = surfaceOutcomeArmContract witness
    outcomeClass = callableOutcomeClass contract
    continuation disposition = SurfaceCallableOutcomeContinuation
      { surfaceContinuationInvocationSpan = surfaceOutcomeArmInvocationSpan witness
      , surfaceContinuationArmSpan = surfaceOutcomeArmSpan witness
      , surfaceContinuationDeclarationKey = surfaceOutcomeArmDeclarationKey witness
      , surfaceContinuationSourceLabel = surfaceOutcomeArmSourceLabel witness
      , surfaceContinuationPayload = surfaceOutcomeArmPayload witness
      , surfaceContinuationOutcomeClass = outcomeClass
      , surfaceContinuationDisposition = disposition
      , surfaceContinuationState = callableOutcomeState contract
      , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition contract
      , surfaceContinuationPostconditions = callableOutcomePostconditions contract
      , surfaceContinuationResidualObligations = callableOutcomeResidualObligations contract
      , surfaceContinuationAssumptions = callableOutcomeAssumptions contract
      , surfaceContinuationEffects = callableOutcomeEffects contract
      , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts contract
      , surfaceContinuationContract = contract
      }
