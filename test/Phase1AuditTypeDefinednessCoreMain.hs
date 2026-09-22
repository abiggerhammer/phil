{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Phase1AuditTypeDefinednessCommon
import qualified Data.Map.Strict as Map
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Discharge
  ( DischargeError (..), ObligationDisposition (..), ResolvedObligation (..)
  , StaticDischarge (..), emptyDischargePolicy, resolveObligation )
import Phil.Core.Focusing
  ( FocusMechanism (..), FocusPlan (..), FocusedRequirement (..), FocusingError (..)
  , canonicalizeProposition, focusProposition )
import Phil.Core.Refinement
  ( RefinementError (..), ResidualSpec (..), dischargeProposition )
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Static (declareOpaqueClaim, emptyStaticContext)
import Phil.Core.Syntax
  ( Name (..), Obligation (..), ObligationId (..), Proposition (..)
  , RefSort (..), RefTerm (..), Ty (..), Value (..) )
import qualified Phil.Core.Syntax as Syntax
import Phil.Core.Value
  ( ValueError (..), ValueResult (..), checkValue, checkValueWithResidual, synthValue )

main :: IO ()
main = runCases checks observations

checks :: Mode -> [(String, Result)]
checks mode =
  [ ("C01", checkFalse (checkValue (VBool False) (refined badPredicate) emptyCheckState))
  , ("C02", do
        let safe = RefSub (RefNat 5) (RefNat 3)
        result <- right (checkValue (VBool False) (refined (Equal safe safe)) emptyCheckState)
        noResidual result)
  , ("C03", case dischargeProposition (Equal (RefNat 1) (RefBool True)) emptyCheckState of
        Left (RefinementSortError (EqualitySortMismatch SortNat SortBool)) -> Right ()
        other -> Left (show other))
  , ("C04", symbolicResidual)
  , ("C05", canonicalizationBoundary mode)
  , ("C06", proofTypeBoundary mode)
  , ("C07", bytesIndexBoundary mode)
  , ("C08", do
        context <- sameContext
        state <- boolState
        (canonical, _) <- right (canonicalizeProposition context state call)
        eq canonical (if mode == Characterize then Truth else wanted))
  , ("C09", obligationBoundary mode)
  , ("C10", do
        context <- namedContext "Same" (Name "r")
        state <- boolState
        (canonical, _) <- right (canonicalizeProposition context state call)
        eq canonical wanted)
  , ("C11", do
        context <- right (declareOpaqueClaim "Same" [(Name "p",SortBool),(q,SortBool)] emptyStaticContext)
        state <- boolState
        plan <- right (focusProposition context state call)
        eq (focusedCanonical (focusGoal plan)) call
        eq (focusedMechanism (focusGoal plan)) FocusNeedsExplicitMechanism)
  , ("C12", do
        context <- sameContext
        case canonicalizeProposition context emptyCheckState (Atom "Same" [RefBool True]) of
          Left (ClaimArityMismatch "Same" 2 1) -> Right ()
          other -> Left (show other))
  , ("C13", do
        context <- sameContext
        case canonicalizeProposition context emptyCheckState (Atom "Same" [RefNat 0,RefBool True]) of
          Left (ClaimArgumentSortMismatch "Same" 0 SortBool SortNat) -> Right ()
          other -> Left (show other))
  , ("C14", checkFalse (checkValue (VBool False)
        (TyRefined q TyBool (Equal (RefVar q) (RefBool True))) emptyCheckState))
  , ("C15", flatResidual)
  , ("C16", outerResidual)
  , ("C17", do
        result <- right (checkValue (VBool False) (TyRefined q (refined Truth) Truth) emptyCheckState)
        noResidual result)
  , ("C18", do
        state <- truthState
        result <- right (synthValue (VAscribe (VVar (Name "proof"))
          (TyProof (Equal (RefNat 7) (RefNat 7)))) state)
        eq (valueResultType result) (TyProof (Equal (RefNat 7) (RefNat 7)))
        eq (valueResultState result) state)
  , ("C19", do
        context <- namedContext "Same" (Name "r")
        state <- boolState
        case resolveObligation context state emptyDischargePolicy obligation of
          Left (UnresolvedObligation ident proposition) -> do
            eq ident (ObligationId "audit.same")
            eq proposition wanted
          other -> Left (show other))
  ]

call, wanted :: Proposition
call = Atom "Same" [RefVar q, RefBool True]
wanted = Equal (RefVar q) (RefBool True)

obligation :: Obligation
obligation = Obligation (ObligationId "audit.same") call "audit" "scope" "before-use"

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

canonicalizationBoundary :: Mode -> Result
canonicalizationBoundary mode = case canonicalizeProposition emptyStaticContext emptyCheckState badPredicate of
  Left (StaticallyFalseGoal _) | mode == Regression -> Right ()
  Left other -> Left ("unexpected canonicalizer rejection: " <> show other)
  Right (canonical, _) ->
    let result = checkValue (VBool False) (refined canonical) emptyCheckState
    in if mode == Characterize then do
         eq canonical Truth
         accepted <- right result
         eq (valueResultType accepted) (refined Truth)
         noResidual accepted
       else checkFalse result

truthState :: Either String CheckState
truthState = do
  resources <- right (insertBinding Syntax.Unrestricted (Name "proof") (TyProof Truth)
    (resourceContext emptyCheckState))
  pure emptyCheckState { resourceContext = resources }

proofTypeBoundary :: Mode -> Result
proofTypeBoundary mode = do
  state <- truthState
  let target = TyProof badPredicate
      result = synthValue (VAscribe (VVar (Name "proof")) target) state
  if mode == Characterize then do
    accepted <- right result
    eq (valueResultType accepted) target
    eq (valueResultState accepted) state
  else checkFalse result

bytesIndexBoundary :: Mode -> Result
bytesIndexBoundary mode = do
  resources <- right (insertBinding Syntax.Linear (Name "bytes") (TyBytes (RefNat 0))
    (resourceContext emptyCheckState))
  let state = emptyCheckState { resourceContext = resources }
      target = TyBytes (RefScale 0 bad)
      result = checkValue (VVar (Name "bytes")) target state
  if mode == Characterize then do
    accepted <- right result
    eq (valueResultType accepted) target
    eq (valueResultMode accepted) (Just Syntax.Linear)
    eq (valueResultState accepted) emptyCheckState
  else checkFalse result

obligationBoundary :: Mode -> Result
obligationBoundary mode = do
  context <- sameContext
  state <- boolState
  case resolveObligation context state emptyDischargePolicy obligation of
    Right resolved | mode == Characterize -> do
      eq (resolvedObligation resolved) obligation
      eq (resolvedCanonicalProposition resolved) Truth
      eq (resolvedPrerequisites resolved) []
      eq (resolvedDisposition resolved) (StaticallyDischarged StaticByDefinition)
    Left (UnresolvedObligation ident proposition) | mode == Regression -> do
      eq ident (ObligationId "audit.same")
      eq proposition wanted
    other -> Left (show other)

spec :: ResidualSpec
spec = ResidualSpec (ObligationId "audit.nested") "audit-origin" "audit-scope" "before-use"

need :: Proposition
need = Atom "Need" [RefBool False]

flatResidual :: Result
flatResidual = do
  result <- right (checkValueWithResidual spec (VBool False) (refined need) emptyCheckState)
  eq (Map.elems (residualObligations (valueResultState result)))
    [Obligation (ObligationId "audit.nested") need "audit-origin" "audit-scope" "before-use"]

outerResidual :: Result
outerResidual = do
  result <- right (checkValueWithResidual spec (VBool False)
    (TyRefined q (refined Truth) need) emptyCheckState)
  eq (Map.elems (residualObligations (valueResultState result)))
    [Obligation (ObligationId "audit.nested") need "audit-origin" "audit-scope" "before-use"]

symbolicResidual :: Result
symbolicResidual = do
  let a = RefOpaque SortNat "a"
      b = RefOpaque SortNat "b"
      diff = RefSub a b
      predicate = Equal diff diff
  result <- right (checkValueWithResidual spec (VBool False) (refined predicate) emptyCheckState)
  eq (Map.elems (residualObligations (valueResultState result)))
    [Obligation (ObligationId "audit.nested.nat-sub.1") (LessEqual b a)
      "audit-origin" "audit-scope" "before-use"]

-- Observation only: no assertion of a promised nested-residual API contract.
observations :: [(String, Result)]
observations =
  [ ("O01", case checkValueWithResidual spec (VBool False)
       (TyRefined q (refined need) Truth) emptyCheckState of
         Left (ValueRefinementError (MissingEvidence actual)) -> eq actual need
         other -> Left (show other))
  ]
