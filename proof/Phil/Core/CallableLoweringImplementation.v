From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import CallableLowering.

(*
  PHIL-CALL-LOWER-IMPL-001 — executable production correspondence for CALL-016.

  The existing Haskell checker has one known correspondence gap relative to the
  certified model: its source/target lowering records do not yet carry the
  callable machine-shape coordinate bundled into CallableRefinementSurface.
  The production-refinement kernel therefore includes that coordinate explicitly;
  the final binding tranche must strengthen Haskell to supply/check it before this
  obligation may become Implementation Refined.
*)

Record CallableLoweringProjection : Type := mkCallableLoweringProjection {
  projectionContractRevisionEqual : bool;
  projectionMachineShapeEqual : bool;
  projectionOccurrenceEqual : bool;
  projectionStructuralModeEqual : bool;
  projectionCapturesEqual : bool;
  projectionCalleeTransitionEqual : bool;
  projectionCallerAuthorityEqual : bool;
  projectionInternalAuthorityEqual : bool;
  projectionEffectBoundEqual : bool;
  projectionFailuresEqual : bool;
  projectionLoanScopesEqual : bool;
  projectionEffectAccountingEqual : bool;
  projectionFailureAccountingEqual : bool;
  projectionAssumptionAccountingEqual : bool;
  projectionCarrierAccountingEqual : bool;
  projectionCostAccountingEqual : bool
}.

Definition projectionBits (projection : CallableLoweringProjection) : list bool :=
  [ projectionContractRevisionEqual projection
  ; projectionMachineShapeEqual projection
  ; projectionOccurrenceEqual projection
  ; projectionStructuralModeEqual projection
  ; projectionCapturesEqual projection
  ; projectionCalleeTransitionEqual projection
  ; projectionCallerAuthorityEqual projection
  ; projectionInternalAuthorityEqual projection
  ; projectionEffectBoundEqual projection
  ; projectionFailuresEqual projection
  ; projectionLoanScopesEqual projection
  ; projectionEffectAccountingEqual projection
  ; projectionFailureAccountingEqual projection
  ; projectionAssumptionAccountingEqual projection
  ; projectionCarrierAccountingEqual projection
  ; projectionCostAccountingEqual projection
  ].

Fixpoint allTrue (bits : list bool) : Prop :=
  match bits with
  | nil => True
  | bit :: rest => bit = true /\ allTrue rest
  end.

Fixpoint allTrueb (bits : list bool) : bool :=
  match bits with
  | nil => true
  | bit :: rest => bit && allTrueb rest
  end.

Lemma all_trueb_true_iff :
  forall bits, allTrueb bits = true <-> allTrue bits.
Proof.
  induction bits as [| bit rest IH].
  - cbn. tauto.
  - cbn. rewrite andb_true_iff. rewrite IH. tauto.
Qed.

Definition ProductionCallableLoweringAccepts
  (projection : CallableLoweringProjection) : Prop :=
  allTrue (projectionBits projection).

Inductive CallableLoweringDecision : Type :=
| CallableLoweringAccepted
| CallableLoweringContractRevisionMismatch
| CallableLoweringMachineShapeMismatch
| CallableLoweringOccurrenceMismatch
| CallableLoweringStructuralModeMismatch
| CallableLoweringCaptureMismatch
| CallableLoweringCalleeTransitionMismatch
| CallableLoweringCallerAuthorityMismatch
| CallableLoweringInternalAuthorityMismatch
| CallableLoweringEffectBoundMismatch
| CallableLoweringFailureMismatch
| CallableLoweringLoanScopeMismatch
| CallableLoweringEffectAccountingMismatch
| CallableLoweringFailureAccountingMismatch
| CallableLoweringAssumptionAccountingMismatch
| CallableLoweringCarrierAccountingMismatch
| CallableLoweringCostAccountingMismatch.

Definition decideCallableLowering
  (projection : CallableLoweringProjection) : CallableLoweringDecision :=
  if projectionContractRevisionEqual projection then
    if projectionMachineShapeEqual projection then
      if projectionOccurrenceEqual projection then
        if projectionStructuralModeEqual projection then
          if projectionCapturesEqual projection then
            if projectionCalleeTransitionEqual projection then
              if projectionCallerAuthorityEqual projection then
                if projectionInternalAuthorityEqual projection then
                  if projectionEffectBoundEqual projection then
                    if projectionFailuresEqual projection then
                      if projectionLoanScopesEqual projection then
                        if projectionEffectAccountingEqual projection then
                          if projectionFailureAccountingEqual projection then
                            if projectionAssumptionAccountingEqual projection then
                              if projectionCarrierAccountingEqual projection then
                                if projectionCostAccountingEqual projection then
                                  CallableLoweringAccepted
                                else CallableLoweringCostAccountingMismatch
                              else CallableLoweringCarrierAccountingMismatch
                            else CallableLoweringAssumptionAccountingMismatch
                          else CallableLoweringFailureAccountingMismatch
                        else CallableLoweringEffectAccountingMismatch
                      else CallableLoweringLoanScopeMismatch
                    else CallableLoweringFailureMismatch
                  else CallableLoweringEffectBoundMismatch
                else CallableLoweringInternalAuthorityMismatch
              else CallableLoweringCallerAuthorityMismatch
            else CallableLoweringCalleeTransitionMismatch
          else CallableLoweringCaptureMismatch
        else CallableLoweringStructuralModeMismatch
      else CallableLoweringOccurrenceMismatch
    else CallableLoweringMachineShapeMismatch
  else CallableLoweringContractRevisionMismatch.

Definition loweringDecisionAcceptedb (decision : CallableLoweringDecision) : bool :=
  match decision with
  | CallableLoweringAccepted => true
  | _ => false
  end.

Theorem lowering_decision_acceptedb_matches_projection :
  forall projection,
    loweringDecisionAcceptedb (decideCallableLowering projection) =
      allTrueb (projectionBits projection).
Proof.
  intros [contract machine occurrence mode captures transition caller internal
          effects failures loans accountEffects accountFailures accountAssumptions
          accountCarriers accountCost].
  cbn.
  destruct contract, machine, occurrence, mode, captures, transition, caller,
    internal, effects, failures, loans, accountEffects, accountFailures,
    accountAssumptions, accountCarriers, accountCost; reflexivity.
Qed.

Theorem lowering_decision_accept_iff_projection_accepts :
  forall projection,
    decideCallableLowering projection = CallableLoweringAccepted <->
    ProductionCallableLoweringAccepts projection.
Proof.
  intro projection.
  unfold ProductionCallableLoweringAccepts.
  split.
  - intro Haccepted.
    apply (proj1 (all_trueb_true_iff (projectionBits projection))).
    rewrite <- lowering_decision_acceptedb_matches_projection.
    rewrite Haccepted.
    reflexivity.
  - intro Haccepts.
    destruct projection as
      [contract machine occurrence mode captures transition caller internal
       effects failures loans accountEffects accountFailures accountAssumptions
       accountCarriers accountCost].
    cbn in Haccepts |- *.
    destruct Haccepts as
      [Hcontract [Hmachine [Hoccurrence [Hmode [Hcaptures [Htransition
       [Hcaller [Hinternal [Heffects [Hfailures [Hloans [HaccountEffects
       [HaccountFailures [HaccountAssumptions [HaccountCarriers [HaccountCost _]]]]]]]]]]]]]]]].
    rewrite Hcontract, Hmachine, Hoccurrence, Hmode, Hcaptures, Htransition,
      Hcaller, Hinternal, Heffects, Hfailures, Hloans, HaccountEffects,
      HaccountFailures, HaccountAssumptions, HaccountCarriers, HaccountCost.
    reflexivity.
Qed.

Theorem accepted_production_lowering_refines_call016 :
  forall source target accounting projection,
    (projectionContractRevisionEqual projection = true ->
     projectionMachineShapeEqual projection = true ->
     projectionCalleeTransitionEqual projection = true ->
     projectionCallerAuthorityEqual projection = true ->
     projectionEffectBoundEqual projection = true ->
     projectionFailuresEqual projection = true ->
     targetLoweringSurface target = sourceLoweringSurface source) ->
    (projectionOccurrenceEqual projection = true ->
     targetLoweringOccurrence target = sourceLoweringOccurrence source) ->
    (projectionStructuralModeEqual projection = true ->
     targetLoweringMode target = sourceLoweringMode source) ->
    (projectionCapturesEqual projection = true ->
     targetLoweringCaptures target = sourceLoweringCaptures source) ->
    (projectionInternalAuthorityEqual projection = true ->
     targetLoweringInternalAuthority target = sourceLoweringInternalAuthority source) ->
    (projectionLoanScopesEqual projection = true ->
     targetLoweringLoans target = sourceLoweringLoans source) ->
    (projectionEffectAccountingEqual projection = true ->
     accountedEffects accounting = targetIntroducedEffects target) ->
    (projectionFailureAccountingEqual projection = true ->
     accountedFailures accounting = targetIntroducedFailures target) ->
    (projectionAssumptionAccountingEqual projection = true ->
     accountedAssumptions accounting = targetIntroducedAssumptions target) ->
    (projectionCarrierAccountingEqual projection = true ->
     accountedCarriers accounting = targetIntroducedCarriers target) ->
    (projectionCostAccountingEqual projection = true ->
     accountedCost accounting = targetIntroducedCost target) ->
    decideCallableLowering projection = CallableLoweringAccepted ->
    CallableLoweringAccepts source target accounting.
Proof.
  intros source target accounting projection
    Hsurface Hoccurrence Hmode Hcaptures Hinternal Hloans
    HaccountEffects HaccountFailures HaccountAssumptions HaccountCarriers HaccountCost
    Hdecision.
  pose proof (proj1
    (lowering_decision_accept_iff_projection_accepts projection) Hdecision)
    as Haccepts.
  destruct projection as
    [contract machine occurrence mode captures transition caller internal
     effects failures loans accountEffects accountFailures accountAssumptions
     accountCarriers accountCost].
  cbn in Haccepts |- *.
  destruct Haccepts as
    [Hcontract [Hmachine [HoccurrenceBit [HmodeBit [HcapturesBit [Htransition
     [Hcaller [HinternalBit [Heffects [Hfailures [HloansBit [HaccountEffectsBit
     [HaccountFailuresBit [HaccountAssumptionsBit [HaccountCarriersBit
      [HaccountCostBit _]]]]]]]]]]]]]]]].
  split.
  - eapply Hsurface; eauto.
  - split.
    + apply Hoccurrence. exact HoccurrenceBit.
    + split.
      * apply Hmode. exact HmodeBit.
      * split.
        -- apply Hcaptures. exact HcapturesBit.
        -- split.
           ++ apply Hinternal. exact HinternalBit.
           ++ split.
              ** apply Hloans. exact HloansBit.
              ** split.
                 --- apply HaccountEffects. exact HaccountEffectsBit.
                 --- split.
                     +++ apply HaccountFailures. exact HaccountFailuresBit.
                     +++ split.
                         *** apply HaccountAssumptions. exact HaccountAssumptionsBit.
                         *** split.
                             ---- apply HaccountCarriers. exact HaccountCarriersBit.
                             ---- apply HaccountCost. exact HaccountCostBit.
Qed.
