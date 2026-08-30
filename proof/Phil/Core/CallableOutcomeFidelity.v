From Stdlib Require Import Arith.PeanoNat Bool.Bool.

(*
  PHIL-CALL-OUTCOME-001 — exact callable outcome classification and residual
  obligation fidelity.

  This normalized model starts after concrete list normalization into one exact
  outcome-class domain.  State, callee transition, and each semantic bucket are
  represented by canonical semantic identities.  Concrete Haskell Map/Set
  construction, ordering, duplicate detection, Text/Outcome representation,
  and diagnostic reconstruction remain explicit implementation correspondence
  boundaries.
*)

Inductive OutcomeBucket : Type :=
| OutcomePostconditionBucket
| OutcomeAssumptionBucket
| OutcomeEffectBucket
| OutcomeDischargedFactBucket.

(*
  The concrete checker computes this disposition from a missing expected
  residual obligation and membership in the actual semantic buckets.  Keeping
  that lookup as an explicit disposition lets the proof state the semantic
  non-laundering rule without pretending to prove Data.Set implementation
  correspondence.
*)
Inductive ResidualDisposition : Type :=
| ResidualExact
| ResidualReclassified : OutcomeBucket -> ResidualDisposition
| ResidualMismatch.

Inductive CallableOutcomeError : Type :=
| CallableOutcomeClassSetMismatch
| CallableOutcomeStateMismatch
| CallableOutcomeCalleeTransitionMismatch
| CallableResidualObligationReclassified : OutcomeBucket -> CallableOutcomeError
| CallableResidualObligationMismatch
| CallableOutcomePostconditionMismatch
| CallableOutcomeAssumptionMismatch
| CallableOutcomeEffectMismatch
| CallableOutcomeDischargedFactMismatch.

Inductive CallableOutcomeResult : Type :=
| CallableOutcomeFailure : CallableOutcomeError -> CallableOutcomeResult
| CallableOutcomeSuccess : CallableOutcomeResult.

Definition checkOutcomeBranch
  (expectedState actualState
   expectedTransition actualTransition
   expectedPostconditions actualPostconditions
   expectedResidual actualResidual
   expectedAssumptions actualAssumptions
   expectedEffects actualEffects
   expectedDischarged actualDischarged : nat)
  (residualDisposition : ResidualDisposition)
  : CallableOutcomeResult :=
  if Nat.eqb expectedState actualState then
    if Nat.eqb expectedTransition actualTransition then
      match residualDisposition with
      | ResidualReclassified bucket =>
          CallableOutcomeFailure (CallableResidualObligationReclassified bucket)
      | ResidualMismatch =>
          CallableOutcomeFailure CallableResidualObligationMismatch
      | ResidualExact =>
          if Nat.eqb expectedResidual actualResidual then
            if Nat.eqb expectedPostconditions actualPostconditions then
              if Nat.eqb expectedAssumptions actualAssumptions then
                if Nat.eqb expectedEffects actualEffects then
                  if Nat.eqb expectedDischarged actualDischarged then
                    CallableOutcomeSuccess
                  else CallableOutcomeFailure CallableOutcomeDischargedFactMismatch
                else CallableOutcomeFailure CallableOutcomeEffectMismatch
              else CallableOutcomeFailure CallableOutcomeAssumptionMismatch
            else CallableOutcomeFailure CallableOutcomePostconditionMismatch
          else CallableOutcomeFailure CallableResidualObligationMismatch
      end
    else CallableOutcomeFailure CallableOutcomeCalleeTransitionMismatch
  else CallableOutcomeFailure CallableOutcomeStateMismatch.

Definition checkCallableOutcomeContract
  (expectedClassDomain actualClassDomain : nat)
  (branchResult : CallableOutcomeResult)
  : CallableOutcomeResult :=
  if Nat.eqb expectedClassDomain actualClassDomain then
    branchResult
  else CallableOutcomeFailure CallableOutcomeClassSetMismatch.

Theorem class_domain_mismatch_rejects_exactly :
  forall expectedDomain actualDomain branchResult,
    expectedDomain <> actualDomain ->
    checkCallableOutcomeContract expectedDomain actualDomain branchResult =
      CallableOutcomeFailure CallableOutcomeClassSetMismatch.
Proof.
  intros expectedDomain actualDomain branchResult Hneq.
  unfold checkCallableOutcomeContract.
  destruct (Nat.eqb expectedDomain actualDomain) eqn:Hdomain.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedDomain actualDomain)) Hdomain).
  - reflexivity.
Qed.

Theorem exact_class_domain_delegates_unchanged :
  forall domain branchResult,
    checkCallableOutcomeContract domain domain branchResult = branchResult.
Proof.
  intros domain branchResult.
  unfold checkCallableOutcomeContract.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem state_mismatch_rejects_exactly :
  forall expectedState actualState
         expectedTransition actualTransition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged disposition,
    expectedState <> actualState ->
    checkOutcomeBranch
      expectedState actualState expectedTransition actualTransition
      expectedPostconditions actualPostconditions expectedResidual actualResidual
      expectedAssumptions actualAssumptions expectedEffects actualEffects
      expectedDischarged actualDischarged disposition =
    CallableOutcomeFailure CallableOutcomeStateMismatch.
Proof.
  intros expectedState actualState
    expectedTransition actualTransition
    expectedPostconditions actualPostconditions
    expectedResidual actualResidual
    expectedAssumptions actualAssumptions
    expectedEffects actualEffects
    expectedDischarged actualDischarged disposition Hneq.
  unfold checkOutcomeBranch.
  destruct (Nat.eqb expectedState actualState) eqn:Hstate.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedState actualState)) Hstate).
  - reflexivity.
Qed.

Theorem transition_mismatch_rejects_exactly :
  forall state expectedTransition actualTransition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged disposition,
    expectedTransition <> actualTransition ->
    checkOutcomeBranch
      state state expectedTransition actualTransition
      expectedPostconditions actualPostconditions expectedResidual actualResidual
      expectedAssumptions actualAssumptions expectedEffects actualEffects
      expectedDischarged actualDischarged disposition =
    CallableOutcomeFailure CallableOutcomeCalleeTransitionMismatch.
Proof.
  intros state expectedTransition actualTransition
    expectedPostconditions actualPostconditions
    expectedResidual actualResidual
    expectedAssumptions actualAssumptions
    expectedEffects actualEffects
    expectedDischarged actualDischarged disposition Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl.
  destruct (Nat.eqb expectedTransition actualTransition) eqn:Htransition.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedTransition actualTransition)) Htransition).
  - reflexivity.
Qed.

Theorem residual_reclassification_rejects_exact_bucket :
  forall state transition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged bucket,
    checkOutcomeBranch
      state state transition transition
      expectedPostconditions actualPostconditions expectedResidual actualResidual
      expectedAssumptions actualAssumptions expectedEffects actualEffects
      expectedDischarged actualDischarged (ResidualReclassified bucket) =
    CallableOutcomeFailure (CallableResidualObligationReclassified bucket).
Proof.
  intros.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  reflexivity.
Qed.

Theorem residual_mismatch_rejects_without_reclassification :
  forall state transition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged,
    checkOutcomeBranch
      state state transition transition
      expectedPostconditions actualPostconditions expectedResidual actualResidual
      expectedAssumptions actualAssumptions expectedEffects actualEffects
      expectedDischarged actualDischarged ResidualMismatch =
    CallableOutcomeFailure CallableResidualObligationMismatch.
Proof.
  intros.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  reflexivity.
Qed.

Theorem exact_disposition_still_requires_exact_residual_set :
  forall state transition postconditions
         expectedResidual actualResidual assumptions effects discharged,
    expectedResidual <> actualResidual ->
    checkOutcomeBranch
      state state transition transition
      postconditions postconditions expectedResidual actualResidual
      assumptions assumptions effects effects discharged discharged ResidualExact =
    CallableOutcomeFailure CallableResidualObligationMismatch.
Proof.
  intros state transition postconditions
    expectedResidual actualResidual assumptions effects discharged Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl.
  destruct (Nat.eqb expectedResidual actualResidual) eqn:Hresidual.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedResidual actualResidual)) Hresidual).
  - reflexivity.
Qed.

Theorem postcondition_mismatch_rejects_exactly :
  forall state transition expectedPostconditions actualPostconditions
         residual assumptions effects discharged,
    expectedPostconditions <> actualPostconditions ->
    checkOutcomeBranch
      state state transition transition
      expectedPostconditions actualPostconditions residual residual
      assumptions assumptions effects effects discharged discharged ResidualExact =
    CallableOutcomeFailure CallableOutcomePostconditionMismatch.
Proof.
  intros state transition expectedPostconditions actualPostconditions
    residual assumptions effects discharged Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl.
  destruct (Nat.eqb expectedPostconditions actualPostconditions) eqn:Hpost.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedPostconditions actualPostconditions)) Hpost).
  - reflexivity.
Qed.

Theorem assumption_mismatch_rejects_exactly :
  forall state transition postconditions residual
         expectedAssumptions actualAssumptions effects discharged,
    expectedAssumptions <> actualAssumptions ->
    checkOutcomeBranch
      state state transition transition
      postconditions postconditions residual residual
      expectedAssumptions actualAssumptions effects effects
      discharged discharged ResidualExact =
    CallableOutcomeFailure CallableOutcomeAssumptionMismatch.
Proof.
  intros state transition postconditions residual
    expectedAssumptions actualAssumptions effects discharged Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl.
  destruct (Nat.eqb expectedAssumptions actualAssumptions) eqn:Hassumption.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedAssumptions actualAssumptions)) Hassumption).
  - reflexivity.
Qed.

Theorem effect_mismatch_rejects_exactly :
  forall state transition postconditions residual assumptions
         expectedEffects actualEffects discharged,
    expectedEffects <> actualEffects ->
    checkOutcomeBranch
      state state transition transition
      postconditions postconditions residual residual
      assumptions assumptions expectedEffects actualEffects
      discharged discharged ResidualExact =
    CallableOutcomeFailure CallableOutcomeEffectMismatch.
Proof.
  intros state transition postconditions residual assumptions
    expectedEffects actualEffects discharged Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl.
  destruct (Nat.eqb expectedEffects actualEffects) eqn:Heffect.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedEffects actualEffects)) Heffect).
  - reflexivity.
Qed.

Theorem discharged_fact_mismatch_rejects_exactly :
  forall state transition postconditions residual assumptions effects
         expectedDischarged actualDischarged,
    expectedDischarged <> actualDischarged ->
    checkOutcomeBranch
      state state transition transition
      postconditions postconditions residual residual
      assumptions assumptions effects effects
      expectedDischarged actualDischarged ResidualExact =
    CallableOutcomeFailure CallableOutcomeDischargedFactMismatch.
Proof.
  intros state transition postconditions residual assumptions effects
    expectedDischarged actualDischarged Hneq.
  unfold checkOutcomeBranch.
  rewrite Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl, Nat.eqb_refl,
    Nat.eqb_refl, Nat.eqb_refl.
  destruct (Nat.eqb expectedDischarged actualDischarged) eqn:Hdischarged.
  - exfalso.
    apply Hneq.
    exact ((proj1 (Nat.eqb_eq expectedDischarged actualDischarged)) Hdischarged).
  - reflexivity.
Qed.

Theorem exact_branch_accepts :
  forall state transition postconditions residual assumptions effects discharged,
    checkOutcomeBranch
      state state transition transition
      postconditions postconditions residual residual
      assumptions assumptions effects effects discharged discharged ResidualExact =
    CallableOutcomeSuccess.
Proof.
  intros.
  unfold checkOutcomeBranch.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem successful_branch_is_exact :
  forall expectedState actualState
         expectedTransition actualTransition
         expectedPostconditions actualPostconditions
         expectedResidual actualResidual
         expectedAssumptions actualAssumptions
         expectedEffects actualEffects
         expectedDischarged actualDischarged disposition,
    checkOutcomeBranch
      expectedState actualState expectedTransition actualTransition
      expectedPostconditions actualPostconditions expectedResidual actualResidual
      expectedAssumptions actualAssumptions expectedEffects actualEffects
      expectedDischarged actualDischarged disposition =
    CallableOutcomeSuccess ->
    expectedState = actualState /\
    expectedTransition = actualTransition /\
    disposition = ResidualExact /\
    expectedResidual = actualResidual /\
    expectedPostconditions = actualPostconditions /\
    expectedAssumptions = actualAssumptions /\
    expectedEffects = actualEffects /\
    expectedDischarged = actualDischarged.
Proof.
  intros expectedState actualState
    expectedTransition actualTransition
    expectedPostconditions actualPostconditions
    expectedResidual actualResidual
    expectedAssumptions actualAssumptions
    expectedEffects actualEffects
    expectedDischarged actualDischarged disposition Hresult.
  unfold checkOutcomeBranch in Hresult.
  destruct (Nat.eqb expectedState actualState) eqn:Hstate; try discriminate.
  destruct (Nat.eqb expectedTransition actualTransition) eqn:Htransition; try discriminate.
  destruct disposition; try discriminate.
  destruct (Nat.eqb expectedResidual actualResidual) eqn:Hresidual; try discriminate.
  destruct (Nat.eqb expectedPostconditions actualPostconditions) eqn:Hpost; try discriminate.
  destruct (Nat.eqb expectedAssumptions actualAssumptions) eqn:Hassumption; try discriminate.
  destruct (Nat.eqb expectedEffects actualEffects) eqn:Heffect; try discriminate.
  destruct (Nat.eqb expectedDischarged actualDischarged) eqn:Hdischarged; try discriminate.
  pose proof ((proj1 (Nat.eqb_eq expectedState actualState)) Hstate) as Estate.
  pose proof ((proj1 (Nat.eqb_eq expectedTransition actualTransition)) Htransition) as Etransition.
  pose proof ((proj1 (Nat.eqb_eq expectedResidual actualResidual)) Hresidual) as Eresidual.
  pose proof ((proj1 (Nat.eqb_eq expectedPostconditions actualPostconditions)) Hpost) as Epost.
  pose proof ((proj1 (Nat.eqb_eq expectedAssumptions actualAssumptions)) Hassumption) as Eassumption.
  pose proof ((proj1 (Nat.eqb_eq expectedEffects actualEffects)) Heffect) as Eeffect.
  pose proof ((proj1 (Nat.eqb_eq expectedDischarged actualDischarged)) Hdischarged) as Edischarged.
  repeat split; try assumption; reflexivity.
Qed.
