{-# LANGUAGE PatternSynonyms #-}

module Phil.Compiler.CallableOutcomeBranchSemantics
  ( SurfaceCallableOutcomeArmSemanticWitness (..)
  , SurfaceCallableOutcomeBranchSemanticError (..)
  , bindSurfaceCallableOutcomeDecision
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBranch (..)
  , SurfaceCallableOutcomeControl (..)
  , SurfaceCallableOutcomeDispatchPlan (..)
  )
import Phil.Core.CallableOutcome
  ( CallableOutcomeClass (..)
  , CallableOutcomeContract
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
  ( CallableOutcomeControlSpec (..)
  , CallableOutcomeSpec (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  )
import Phil.Surface.Syntax
  ( CaseArm (..)
  , CasePattern (..)
  , Located (..)
  , SourceSpan
  , SurfaceExpression (..)
  , pattern InvokeExpression
  )

-- | Exact compiler-side semantic witness for one source arm of a direct
-- `decide invoke`. The complete outcome contract is retained unchanged; source
-- labels and payload telescopes are merely the explicit dispatch binding for
-- that semantic outcome, not a substitute for its state, postconditions,
-- obligations, assumptions, effects, discharged facts, or callee transition.
data SurfaceCallableOutcomeArmSemanticWitness =
  SurfaceCallableOutcomeArmSemanticWitness
    { surfaceOutcomeArmInvocationSpan :: SourceSpan
    , surfaceOutcomeArmSpan :: SourceSpan
    , surfaceOutcomeArmDeclarationKey :: DeclarationKey
    , surfaceOutcomeArmSourceLabel :: Text
    , surfaceOutcomeArmPayload :: [(Mode, Ty)]
    , surfaceOutcomeArmControl :: SurfaceCallableOutcomeControl
    , surfaceOutcomeArmContract :: CallableOutcomeContract
    }
  deriving (Eq, Ord, Show)

data SurfaceCallableOutcomeBranchSemanticError
  = SurfaceCallableOutcomeDecisionExpected SourceSpan
  | SurfaceCallableOutcomeDirectInvokeExpected SourceSpan
  | SurfaceCallableOutcomeInvocationSpanMismatch SourceSpan SourceSpan
  | SurfaceCallableOutcomeDisplayNameMismatch Text Text
  | SurfaceCallableOutcomeUnknownCallable Text
  | SurfaceCallableOutcomeDeclarationMismatch DeclarationKey DeclarationKey
  | SurfaceCallableOutcomeDispatchNotInstalled DeclarationKey
  | SurfaceCallableOutcomeNeutralDispatchMismatch DeclarationKey
  | SurfaceCallableOutcomeDuplicateSourceArm Text
  | SurfaceCallableOutcomeArmDomainMismatch (Set Text) (Set Text)
  | SurfaceCallableOutcomeUnknownSourceArm Text
  deriving (Eq, Ord, Show)

-- | Bind the arms of one already-Surface-checked direct `decide invoke` to the
-- exact CALL-019 semantic branches retained by its dispatch plan.
--
-- This bridge deliberately remains compiler-side. Surface sees only the neutral
-- label/payload/control carrier installed by #968/#973; this function proves
-- that carrier still corresponds exactly to the semantic plan before exposing
-- branch-local complete contracts to successor composition work.
bindSurfaceCallableOutcomeDecision
  :: SurfaceEnvironment
  -> SurfaceCallableOutcomeDispatchPlan
  -> Located SurfaceExpression
  -> Either SurfaceCallableOutcomeBranchSemanticError
       [SurfaceCallableOutcomeArmSemanticWitness]
bindSurfaceCallableOutcomeDecision environment plan decisionExpression = do
  (scrutinee, arms) <- case locatedValue decisionExpression of
    DecideExpression actualScrutinee actualArms -> Right (actualScrutinee, actualArms)
    _ -> Left (SurfaceCallableOutcomeDecisionExpected
      (locatedSpan decisionExpression))
  displayName <- case locatedValue scrutinee of
    InvokeExpression name _ -> Right name
    _ -> Left (SurfaceCallableOutcomeDirectInvokeExpected (locatedSpan scrutinee))

  let invocation = surfaceOutcomeDispatchInvocation plan
      expectedSpan = surfaceSemanticInvocationSpan invocation
      expectedDisplayName = surfaceSemanticInvocationDisplayName invocation
      expectedDeclarationKey = surfaceSemanticInvocationDeclarationKey invocation
  if locatedSpan scrutinee == expectedSpan
    then pure ()
    else Left (SurfaceCallableOutcomeInvocationSpanMismatch
      expectedSpan
      (locatedSpan scrutinee))
  if displayName == expectedDisplayName
    then pure ()
    else Left (SurfaceCallableOutcomeDisplayNameMismatch expectedDisplayName displayName)

  signature <- maybe
    (Left (SurfaceCallableOutcomeUnknownCallable displayName))
    Right
    (Map.lookup displayName (surfaceCallables environment))
  let actualDeclarationKey = surfaceCallableDeclarationKey signature
  if actualDeclarationKey == expectedDeclarationKey
    then pure ()
    else Left (SurfaceCallableOutcomeDeclarationMismatch
      expectedDeclarationKey
      actualDeclarationKey)

  neutral <- maybe
    (Left (SurfaceCallableOutcomeDispatchNotInstalled expectedDeclarationKey))
    Right
    (Map.lookup expectedDeclarationKey (surfaceCallableOutcomes environment))
  if neutralDispatchMatches (surfaceOutcomeDispatchBranches plan) neutral
    then pure ()
    else Left (SurfaceCallableOutcomeNeutralDispatchMismatch expectedDeclarationKey)

  let sourceLabels = map
        (casePatternLabel . caseArmPattern . locatedValue)
        arms
  checkUniqueSourceLabels sourceLabels
  let expectedLabels = Set.fromList (map surfaceOutcomeBranchLabel
        (surfaceOutcomeDispatchBranches plan))
      actualLabels = Set.fromList sourceLabels
  if expectedLabels == actualLabels
    then pure ()
    else Left (SurfaceCallableOutcomeArmDomainMismatch expectedLabels actualLabels)

  mapM (witnessArm expectedSpan expectedDeclarationKey
    (surfaceOutcomeDispatchBranches plan)) arms

checkUniqueSourceLabels
  :: [Text]
  -> Either SurfaceCallableOutcomeBranchSemanticError ()
checkUniqueSourceLabels = go Set.empty
  where
    go _ [] = Right ()
    go seen (label : rest)
      | Set.member label seen = Left (SurfaceCallableOutcomeDuplicateSourceArm label)
      | otherwise = go (Set.insert label seen) rest

neutralDispatchMatches
  :: [SurfaceCallableOutcomeBranch]
  -> [CallableOutcomeSpec]
  -> Bool
neutralDispatchMatches branches specs =
  length branches == length specs
    && and (zipWith neutralBranchMatches branches specs)

neutralBranchMatches
  :: SurfaceCallableOutcomeBranch
  -> CallableOutcomeSpec
  -> Bool
neutralBranchMatches branch spec =
  callableOutcomeLabel spec == surfaceOutcomeBranchLabel branch
    && callableOutcomePayload spec == surfaceOutcomeBranchPayload branch
    && neutralControlMatches branch (callableOutcomeControl spec)

neutralControlMatches
  :: SurfaceCallableOutcomeBranch
  -> CallableOutcomeControlSpec
  -> Bool
neutralControlMatches branch neutralControl =
  case (surfaceOutcomeBranchControl branch, surfaceOutcomeBranchClass branch) of
    (SurfaceCallableOutcomeContinues, CallableSuccessOutcome) ->
      neutralControl == CallableOutcomeContinues
    (SurfaceCallableOutcomeContinues,
        CallableNonSuccessOutcome (CallableTypedNegative _)) ->
      neutralControl == CallableOutcomeContinues
    (SurfaceCallableOutcomeDeclaredTerminal,
        CallableNonSuccessOutcome (CallableDeclaredTerminal outcome)) ->
      neutralControl == CallableOutcomeCloses outcome
    _ -> False

witnessArm
  :: SourceSpan
  -> DeclarationKey
  -> [SurfaceCallableOutcomeBranch]
  -> Located CaseArm
  -> Either SurfaceCallableOutcomeBranchSemanticError
       SurfaceCallableOutcomeArmSemanticWitness
witnessArm invocationSpan declarationKey branches arm = do
  let label = casePatternLabel (caseArmPattern (locatedValue arm))
  branch <- case
      [ candidate
      | candidate <- branches
      , surfaceOutcomeBranchLabel candidate == label
      ] of
    [candidate] -> Right candidate
    _ -> Left (SurfaceCallableOutcomeUnknownSourceArm label)
  pure SurfaceCallableOutcomeArmSemanticWitness
    { surfaceOutcomeArmInvocationSpan = invocationSpan
    , surfaceOutcomeArmSpan = locatedSpan arm
    , surfaceOutcomeArmDeclarationKey = declarationKey
    , surfaceOutcomeArmSourceLabel = label
    , surfaceOutcomeArmPayload = surfaceOutcomeBranchPayload branch
    , surfaceOutcomeArmControl = surfaceOutcomeBranchControl branch
    , surfaceOutcomeArmContract = surfaceOutcomeBranchContract branch
    }
