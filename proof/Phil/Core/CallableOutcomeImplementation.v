From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Phil.Core Require Import CallableOutcomeFidelity.

(*
  Executable implementation correspondence for PHIL-CALL-OUTCOME-001.

  The concrete Haskell checker remains responsible for list-to-Map
  normalization, duplicate detection, Map/Set identity and membership,
  residual-obligation witness selection, native diagnostics, and concrete
  representation equality. This layer owns the final reflected decision tree
  once those facts have been computed.
*)

Inductive CallableOutcomeDecision : Type :=
| CallableOutcomeClassSetDecision
| CallableOutcomeStateDecision
| CallableOutcomeCalleeTransitionDecision
| CallableResidualObligationReclassifiedDecision
    (bucket : OutcomeBucket)
| CallableResidualObligationMismatchDecision
| CallableOutcomePostconditionDecision
| CallableOutcomeAssumptionDecision
| CallableOutcomeEffectDecision
| CallableOutcomeDischargedFactDecision
| CallableOutcomeAcceptedDecision.

Definition decideCallableOutcomeByFacts
  (classDomainExact
   stateExact
   transitionExact
   residualExact
   postconditionsExact
   assumptionsExact
   effectsExact
   dischargedFactsExact : bool)
  (residualDisposition : ResidualDisposition)
  : CallableOutcomeDecision :=
  if classDomainExact then
    if stateExact then
      if transitionExact then
        match residualDisposition with
        | ResidualReclassified bucket =>
            CallableResidualObligationReclassifiedDecision bucket
        | ResidualMismatch =>
            CallableResidualObligationMismatchDecision
        | ResidualExact =>
            if residualExact then
              if postconditionsExact then
                if assumptionsExact then
                  if effectsExact then
                    if dischargedFactsExact then
                      CallableOutcomeAcceptedDecision
                    else CallableOutcomeDischargedFactDecision
                  else CallableOutcomeEffectDecision
                else CallableOutcomeAssumptionDecision
              else CallableOutcomePostconditionDecision
            else CallableResidualObligationMismatchDecision
        end
      else CallableOutcomeCalleeTransitionDecision
    else CallableOutcomeStateDecision
  else CallableOutcomeClassSetDecision.

Definition callableOutcomeDecisionResult
  (decision : CallableOutcomeDecision) : CallableOutcomeResult :=
  match decision with
  | CallableOutcomeClassSetDecision =>
      CallableOutcomeFailure CallableOutcomeClassSetMismatch
  | CallableOutcomeStateDecision =>
      CallableOutcomeFailure CallableOutcomeStateMismatch
  | CallableOutcomeCalleeTransitionDecision =>
      CallableOutcomeFailure CallableOutcomeCalleeTransitionMismatch
  | CallableResidualObligationReclassifiedDecision bucket =>
      CallableOutcomeFailure (CallableResidualObligationReclassified bucket)
  | CallableResidualObligationMismatchDecision =>
      CallableOutcomeFailure CallableResidualObligationMismatch
  | CallableOutcomePostconditionDecision =>
      CallableOutcomeFailure CallableOutcomePostconditionMismatch
  | CallableOutcomeAssumptionDecision =>
      CallableOutcomeFailure CallableOutcomeAssumptionMismatch
  | CallableOutcomeEffectDecision =>
      CallableOutcomeFailure CallableOutcomeEffectMismatch
  | CallableOutcomeDischargedFactDecision =>
      CallableOutcomeFailure CallableOutcomeDischargedFactMismatch
  | CallableOutcomeAcceptedDecision => CallableOutcomeSuccess
  end.

Theorem callable_outcome_decision_matches_certified :
  forall classDomainExact stateExact transitionExact residualExact
         postconditionsExact assumptionsExact effectsExact dischargedFactsExact
         residualDisposition
         expectedClassDomain actualClassDomain
         expectedState actualState
         expectedTransition actualTransition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged,
    Nat.eqb expectedClassDomain actualClassDomain = classDomainExact ->
    Nat.eqb expectedState actualState = stateExact ->
    Nat.eqb expectedTransition actualTransition = transitionExact ->
    Nat.eqb expectedResidual actualResidual = residualExact ->
    Nat.eqb expectedPostconditions actualPostconditions = postconditionsExact ->
    Nat.eqb expectedAssumptions actualAssumptions = assumptionsExact ->
    Nat.eqb expectedEffects actualEffects = effectsExact ->
    Nat.eqb expectedDischarged actualDischarged = dischargedFactsExact ->
    callableOutcomeDecisionResult
      (decideCallableOutcomeByFacts
        classDomainExact
        stateExact
        transitionExact
        residualExact
        postconditionsExact
        assumptionsExact
        effectsExact
        dischargedFactsExact
        residualDisposition) =
    checkCallableOutcomeContract
      expectedClassDomain
      actualClassDomain
      (checkOutcomeBranch
        expectedState
        actualState
        expectedTransition
        actualTransition
        expectedPostconditions
        actualPostconditions
        expectedResidual
        actualResidual
        expectedAssumptions
        actualAssumptions
        expectedEffects
        actualEffects
        expectedDischarged
        actualDischarged
        residualDisposition).
Proof.
  intros classDomainExact stateExact transitionExact residualExact
    postconditionsExact assumptionsExact effectsExact dischargedFactsExact
    residualDisposition
    expectedClassDomain actualClassDomain
    expectedState actualState
    expectedTransition actualTransition
    expectedPostconditions actualPostconditions
    expectedResidual actualResidual
    expectedAssumptions actualAssumptions
    expectedEffects actualEffects
    expectedDischarged actualDischarged
    Hclass Hstate Htransition Hresidual Hpost Hassumption Heffect Hdischarged.
  unfold checkCallableOutcomeContract, checkOutcomeBranch.
  rewrite Hclass, Hstate, Htransition, Hresidual, Hpost,
    Hassumption, Heffect, Hdischarged.
  unfold decideCallableOutcomeByFacts, callableOutcomeDecisionResult.
  destruct classDomainExact, stateExact, transitionExact,
    residualExact, postconditionsExact, assumptionsExact,
    effectsExact, dischargedFactsExact, residualDisposition;
    reflexivity.
Qed.
