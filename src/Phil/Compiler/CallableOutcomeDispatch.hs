{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , SurfaceCallableOutcomeControl (..)
  , SurfaceCallableOutcomeBranch (..)
  , SurfaceCallableOutcomeDispatchPlan (..)
  , SurfaceCallableOutcomeDispatchError (..)
  , planSurfaceCallableOutcomeDispatch
  , installSurfaceCallableOutcomeDispatch
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  )
import Phil.Core.CallableRefinement
  ( CallableFailure (..)
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax
  ( Mode
  , Ty
  )
import Phil.Surface.Check
  ( CallableOutcomeSpec (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  )

-- | Explicit source-dispatch binding for one exact callable outcome class.
-- The source label and payload signature are supplied by the competent
-- declaration/elaboration layer; CALL-019 never derives them from diagnostic
-- spellings or from the textual representation of a semantic outcome class.
data SurfaceCallableOutcomeBinding = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass :: CallableOutcomeClass
  , surfaceOutcomeBindingLabel :: Text
  , surfaceOutcomeBindingPayload :: [(Mode, Ty)]
  }
  deriving (Eq, Ord, Show)

-- | Whether a source branch may continue ordinary caller checking. Typed
-- negative outcomes remain ordinary continuing branches; declared-terminal and
-- fatal outcomes do not acquire a fictitious continuation merely because they
-- share the same source case-analysis mechanism.
data SurfaceCallableOutcomeControl
  = SurfaceCallableOutcomeContinues
  | SurfaceCallableOutcomeDeclaredTerminal
  | SurfaceCallableOutcomeFatalTerminal
  deriving (Eq, Ord, Show)

-- | One exact branch of a CALL-019 source dispatch plan. The complete semantic
-- outcome contract is retained unchanged so postconditions, residual
-- obligations, assumptions, effects, discharged facts, state, and callee
-- transition remain branch-local facts for the next composition slice.
data SurfaceCallableOutcomeBranch = SurfaceCallableOutcomeBranch
  { surfaceOutcomeBranchClass :: CallableOutcomeClass
  , surfaceOutcomeBranchLabel :: Text
  , surfaceOutcomeBranchPayload :: [(Mode, Ty)]
  , surfaceOutcomeBranchControl :: SurfaceCallableOutcomeControl
  , surfaceOutcomeBranchContract :: CallableOutcomeContract
  }
  deriving (Eq, Ord, Show)

-- | Ordered source/evaluation dispatch plan for one exact invocation occurrence.
-- Branch order follows the stabilized callable outcome contract rather than Map
-- enumeration order.
data SurfaceCallableOutcomeDispatchPlan = SurfaceCallableOutcomeDispatchPlan
  { surfaceOutcomeDispatchInvocation :: SurfaceCallableInvocationSemanticAccount
  , surfaceOutcomeDispatchBranches :: [SurfaceCallableOutcomeBranch]
  }
  deriving (Eq, Ord, Show)

data SurfaceCallableOutcomeDispatchError
  = SurfaceCallableDuplicateOutcomeClass CallableOutcomeClass
  | SurfaceCallableOutcomeBindingDomainMismatch
      (Set.Set CallableOutcomeClass)
      (Set.Set CallableOutcomeClass)
  | SurfaceCallableOutcomeBindingKeyMismatch
      CallableOutcomeClass
      CallableOutcomeClass
  | SurfaceCallableOutcomeEmptyLabel CallableOutcomeClass
  | SurfaceCallableDuplicateOutcomeLabel Text
  | SurfaceCallableOutcomeUnknownSurfaceCallable Text
  | SurfaceCallableOutcomeDeclarationMismatch DeclarationKey DeclarationKey
  | SurfaceCallableOutcomeDispatchConflict DeclarationKey
  | SurfaceCallableOutcomeControlRequiresSurfaceRepresentation
      CallableOutcomeClass
      SurfaceCallableOutcomeControl
  deriving (Eq, Ord, Show)

-- | Bind the exact semantic branch domain of one invocation to explicit source
-- case labels and payload signatures. The binding domain must be exact: missing
-- branches cannot disappear and extra source branches cannot be invented.
-- Duplicate semantic classes and duplicate source labels reject fail-closed.
planSurfaceCallableOutcomeDispatch
  :: Map CallableOutcomeClass SurfaceCallableOutcomeBinding
  -> SurfaceCallableInvocationSemanticAccount
  -> Either SurfaceCallableOutcomeDispatchError SurfaceCallableOutcomeDispatchPlan
planSurfaceCallableOutcomeDispatch bindings invocation = do
  semanticByClass <- normalizeOutcomes (surfaceSemanticInvocationOutcomes invocation)
  let semanticClasses = Map.keysSet semanticByClass
      bindingClasses = Map.keysSet bindings
  if semanticClasses == bindingClasses
    then pure ()
    else Left
      (SurfaceCallableOutcomeBindingDomainMismatch semanticClasses bindingClasses)
  checkedBindings <- mapM checkBinding (Map.toAscList bindings)
  checkUniqueLabels (map (surfaceOutcomeBindingLabel . snd) checkedBindings)
  branches <- mapM (makeBranch bindings) (surfaceSemanticInvocationOutcomes invocation)
  pure SurfaceCallableOutcomeDispatchPlan
    { surfaceOutcomeDispatchInvocation = invocation
    , surfaceOutcomeDispatchBranches = branches
    }
  where
    checkBinding (key, binding)
      | surfaceOutcomeBindingClass binding /= key =
          Left
            (SurfaceCallableOutcomeBindingKeyMismatch
              key
              (surfaceOutcomeBindingClass binding))
      | surfaceOutcomeBindingLabel binding == "" =
          Left (SurfaceCallableOutcomeEmptyLabel key)
      | otherwise = Right (key, binding)

normalizeOutcomes
  :: [CallableOutcomeContract]
  -> Either SurfaceCallableOutcomeDispatchError
       (Map CallableOutcomeClass CallableOutcomeContract)
normalizeOutcomes = foldl addOutcome (Right Map.empty)
  where
    addOutcome accumulated outcome = do
      normalized <- accumulated
      let outcomeClass = callableOutcomeClass outcome
      if Map.member outcomeClass normalized
        then Left (SurfaceCallableDuplicateOutcomeClass outcomeClass)
        else Right (Map.insert outcomeClass outcome normalized)

checkUniqueLabels
  :: [Text]
  -> Either SurfaceCallableOutcomeDispatchError ()
checkUniqueLabels = go Set.empty
  where
    go _ [] = Right ()
    go seen (label : rest)
      | Set.member label seen = Left (SurfaceCallableDuplicateOutcomeLabel label)
      | otherwise = go (Set.insert label seen) rest

makeBranch
  :: Map CallableOutcomeClass SurfaceCallableOutcomeBinding
  -> CallableOutcomeContract
  -> Either SurfaceCallableOutcomeDispatchError SurfaceCallableOutcomeBranch
makeBranch bindings outcome = do
  let outcomeClass = callableOutcomeClass outcome
  binding <- case Map.lookup outcomeClass bindings of
    Just value -> Right value
    Nothing -> Left
      (SurfaceCallableOutcomeBindingDomainMismatch
        (Set.singleton outcomeClass)
        Set.empty)
  pure SurfaceCallableOutcomeBranch
    { surfaceOutcomeBranchClass = outcomeClass
    , surfaceOutcomeBranchLabel = surfaceOutcomeBindingLabel binding
    , surfaceOutcomeBranchPayload = surfaceOutcomeBindingPayload binding
    , surfaceOutcomeBranchControl = outcomeControl outcomeClass
    , surfaceOutcomeBranchContract = outcome
    }

-- | Install one already checked dispatch plan into the neutral Surface table.
-- The display spelling must still select the exact declaration identity retained
-- by the invocation witness. Reinstalling an identical plan is idempotent; a
-- different plan for the same declaration rejects rather than changing branch
-- meaning after checking.
--
-- The current neutral Surface carrier represents only branch labels and payload
-- telescopes, so it is competent only for branches that really continue caller
-- checking. Declared-terminal and fatal callable outcomes must reject here until
-- Surface has an exact terminal-control carrier; silently installing either as
-- an ordinary decision arm would invent a continuation forbidden by CALL-019.
installSurfaceCallableOutcomeDispatch
  :: SurfaceCallableOutcomeDispatchPlan
  -> SurfaceEnvironment
  -> Either SurfaceCallableOutcomeDispatchError SurfaceEnvironment
installSurfaceCallableOutcomeDispatch plan environment = do
  mapM_ requireSurfaceRepresentable (surfaceOutcomeDispatchBranches plan)
  let invocation = surfaceOutcomeDispatchInvocation plan
      displayName = surfaceSemanticInvocationDisplayName invocation
      declarationKey = surfaceSemanticInvocationDeclarationKey invocation
      specs =
        [ CallableOutcomeSpec
            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch
            , callableOutcomePayload = surfaceOutcomeBranchPayload branch
            }
        | branch <- surfaceOutcomeDispatchBranches plan
        ]
  signature <- maybe
    (Left (SurfaceCallableOutcomeUnknownSurfaceCallable displayName))
    Right
    (Map.lookup displayName (surfaceCallables environment))
  if surfaceCallableDeclarationKey signature == declarationKey
    then pure ()
    else Left
      (SurfaceCallableOutcomeDeclarationMismatch
        declarationKey
        (surfaceCallableDeclarationKey signature))
  case Map.lookup declarationKey (surfaceCallableOutcomes environment) of
    Nothing -> Right environment
      { surfaceCallableOutcomes =
          Map.insert declarationKey specs (surfaceCallableOutcomes environment)
      }
    Just existing
      | existing == specs -> Right environment
      | otherwise -> Left (SurfaceCallableOutcomeDispatchConflict declarationKey)

requireSurfaceRepresentable
  :: SurfaceCallableOutcomeBranch
  -> Either SurfaceCallableOutcomeDispatchError ()
requireSurfaceRepresentable branch =
  case surfaceOutcomeBranchControl branch of
    SurfaceCallableOutcomeContinues -> Right ()
    control -> Left
      (SurfaceCallableOutcomeControlRequiresSurfaceRepresentation
        (surfaceOutcomeBranchClass branch)
        control)

outcomeControl :: CallableOutcomeClass -> SurfaceCallableOutcomeControl
outcomeControl outcomeClass = case outcomeClass of
  CallableSuccessOutcome -> SurfaceCallableOutcomeContinues
  CallableNonSuccessOutcome failure -> case failure of
    CallableTypedNegative _ -> SurfaceCallableOutcomeContinues
    CallableDeclaredTerminal _ -> SurfaceCallableOutcomeDeclaredTerminal
    CallableFatal _ -> SurfaceCallableOutcomeFatalTerminal
