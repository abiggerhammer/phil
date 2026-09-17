module Phil.Compiler.CallableOutcomeBranchResourceInstall
  ( SurfaceCallableOutcomeBranchResourceInstallError (..)
  , installSurfaceCallableOutcomeBranchResources
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeBranchResourceEnvironment (..)
  , SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.Callable (CalleeTransition)
import Phil.Core.CallableOutcome (CallableOutcomeState)
import Phil.Core.Static (DeclarationKey)
import Data.Text (Text)
import Phil.Surface.Check.Types
  ( CallableOutcomeControlSpec (..)
  , CallableOutcomeResourceBinding (..)
  , CallableOutcomeResourceSpec (..)
  , CallableOutcomeSpec (..)
  , SurfaceEnvironment (..)
  )
import Phil.Surface.Syntax (SourceSpan)

data SurfaceCallableOutcomeBranchResourceInstallError
  = SurfaceCallableOutcomeResourceInstallEnvironmentIdentityMismatch SourceSpan
  | SurfaceCallableOutcomeResourceInstallBindingIdentityMismatch
      SourceSpan
      DeclarationKey
      Text
  | SurfaceCallableOutcomeResourceInstallStateMismatch
      SourceSpan
      DeclarationKey
      Text
      CallableOutcomeState
      CallableOutcomeState
  | SurfaceCallableOutcomeResourceInstallCalleeTransitionMismatch
      SourceSpan
      DeclarationKey
      Text
      CalleeTransition
      CalleeTransition
  | SurfaceCallableOutcomeResourceInstallDispatchMissing DeclarationKey
  | SurfaceCallableOutcomeResourceInstallSourceLabelMissing DeclarationKey Text
  | SurfaceCallableOutcomeResourceInstallControlMismatch
      DeclarationKey
      Text
      CallableOutcomeControlSpec
  | SurfaceCallableOutcomeResourceInstallContinuingResidueMissing
      SourceSpan
      DeclarationKey
      Text
  | SurfaceCallableOutcomeResourceInstallTerminalResidueUnsupported
      SourceSpan
      DeclarationKey
      Text
  | SurfaceCallableOutcomeResourceInstallConflict
      SourceSpan
      DeclarationKey
      Text
  deriving (Eq, Show)

-- | Install already-correlated CALL-019 caller resource residues into the
-- occurrence-scoped Surface environment. Compiler semantic-state and callee
-- transition keys are checked here and then erased: Surface receives only the
-- exact binding expectations and active-endpoint selection it is competent to
-- apply through its ordinary structural checker.
installSurfaceCallableOutcomeBranchResources
  :: [SurfaceCallableOutcomeBranchResourceEnvironment]
  -> SurfaceEnvironment
  -> Either SurfaceCallableOutcomeBranchResourceInstallError SurfaceEnvironment
installSurfaceCallableOutcomeBranchResources branchEnvironments initialEnvironment =
  foldM installOne initialEnvironment branchEnvironments
  where
    installOne environment branchEnvironment = do
      let continuation = surfaceBranchResourceContinuation branchEnvironment
          invocationSpan = surfaceBranchResourceInvocationSpan branchEnvironment
          declarationKey = surfaceBranchResourceDeclarationKey branchEnvironment
          sourceLabel = surfaceBranchResourceSourceLabel branchEnvironment
          residue = surfaceBranchResourceResidue branchEnvironment
      if invocationSpan == surfaceContinuationInvocationSpan continuation
          && declarationKey == surfaceContinuationDeclarationKey continuation
          && sourceLabel == surfaceContinuationSourceLabel continuation
        then pure ()
        else Left
          (SurfaceCallableOutcomeResourceInstallEnvironmentIdentityMismatch
            (surfaceBranchResourceArmSpan branchEnvironment))
      specs <- maybe
        (Left (SurfaceCallableOutcomeResourceInstallDispatchMissing declarationKey))
        Right
        (Map.lookup declarationKey (surfaceCallableOutcomes environment))
      spec <- case
          [ candidate
          | candidate <- specs
          , callableOutcomeLabel candidate == sourceLabel
          ] of
        [candidate] -> Right candidate
        _ -> Left
          (SurfaceCallableOutcomeResourceInstallSourceLabelMissing
            declarationKey sourceLabel)
      case surfaceBranchResourceDisposition branchEnvironment of
        SurfaceCallableOutcomeCallerTerminates _ -> do
          case residue of
            Nothing -> pure ()
            Just _ -> Left
              (SurfaceCallableOutcomeResourceInstallTerminalResidueUnsupported
                invocationSpan declarationKey sourceLabel)
          case callableOutcomeControl spec of
            CallableOutcomeCloses _ -> Right environment
            actual -> Left
              (SurfaceCallableOutcomeResourceInstallControlMismatch
                declarationKey sourceLabel actual)
        SurfaceCallableOutcomeCallerFatals _ -> do
          case residue of
            Nothing -> pure ()
            Just _ -> Left
              (SurfaceCallableOutcomeResourceInstallTerminalResidueUnsupported
                invocationSpan declarationKey sourceLabel)
          case callableOutcomeControl spec of
            CallableOutcomeFatals _ -> Right environment
            actual -> Left
              (SurfaceCallableOutcomeResourceInstallControlMismatch
                declarationKey sourceLabel actual)
        SurfaceCallableOutcomeCallerContinues -> do
          binding <- maybe
            (Left
              (SurfaceCallableOutcomeResourceInstallContinuingResidueMissing
                invocationSpan declarationKey sourceLabel))
            Right
            residue
          validateBinding continuation binding
          case callableOutcomeControl spec of
            CallableOutcomeContinues -> pure ()
            actual -> Left
              (SurfaceCallableOutcomeResourceInstallControlMismatch
                declarationKey sourceLabel actual)
          let key = (invocationSpan, declarationKey, sourceLabel)
              neutral = neutralResourceSpec binding
          case Map.lookup key (surfaceCallableOutcomeResources environment) of
            Nothing -> Right environment
              { surfaceCallableOutcomeResources = Map.insert key neutral
                  (surfaceCallableOutcomeResources environment)
              }
            Just existing
              | existing == neutral -> Right environment
              | otherwise -> Left
                  (SurfaceCallableOutcomeResourceInstallConflict
                    invocationSpan declarationKey sourceLabel)

validateBinding
  :: SurfaceCallableOutcomeContinuation
  -> SurfaceCallableOutcomeResourceResidueBinding
  -> Either SurfaceCallableOutcomeBranchResourceInstallError ()
validateBinding continuation binding = do
  let invocationSpan = surfaceContinuationInvocationSpan continuation
      declarationKey = surfaceContinuationDeclarationKey continuation
      sourceLabel = surfaceContinuationSourceLabel continuation
  if surfaceOutcomeResourceInvocationSpan binding == invocationSpan
      && surfaceOutcomeResourceDeclarationKey binding == declarationKey
      && surfaceOutcomeResourceSourceLabel binding == sourceLabel
    then pure ()
    else Left
      (SurfaceCallableOutcomeResourceInstallBindingIdentityMismatch
        invocationSpan declarationKey sourceLabel)
  if surfaceOutcomeResourceState binding == surfaceContinuationState continuation
    then pure ()
    else Left
      (SurfaceCallableOutcomeResourceInstallStateMismatch
        invocationSpan
        declarationKey
        sourceLabel
        (surfaceContinuationState continuation)
        (surfaceOutcomeResourceState binding))
  if surfaceOutcomeResourceCalleeTransition binding
      == surfaceContinuationCalleeTransition continuation
    then pure ()
    else Left
      (SurfaceCallableOutcomeResourceInstallCalleeTransitionMismatch
        invocationSpan
        declarationKey
        sourceLabel
        (surfaceContinuationCalleeTransition continuation)
        (surfaceOutcomeResourceCalleeTransition binding))

neutralResourceSpec
  :: SurfaceCallableOutcomeResourceResidueBinding
  -> CallableOutcomeResourceSpec
neutralResourceSpec binding = CallableOutcomeResourceSpec
  { callableOutcomeResourceBindings =
      Map.map neutralExpectation (surfaceOutcomeResourceBindings binding)
  , callableOutcomeResourceActiveEndpoint =
      surfaceOutcomeResourceActiveEndpoint binding
  }

neutralExpectation
  :: SurfaceCallableOutcomeResourceExpectation
  -> CallableOutcomeResourceBinding
neutralExpectation expectation = case expectation of
  SurfaceCallableResourcePresent meta -> CallableOutcomeResourcePresent meta
  SurfaceCallableResourceAbsent -> CallableOutcomeResourceAbsent
