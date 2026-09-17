From Stdlib Require Import Lists.List.

Import ListNotations.

(*
  PHIL-EXEC-ORDER-001 — deterministic local evaluation order and checked
  target reordering.

  This proof models three semantic boundaries already implemented by EXEC-001,
  EXEC-002, EXEC-003, and EXEC-015:

  - local source execution concatenates statement/strict-child traces in source
    order and stops before any suffix once local control stops;
  - branch choice executes the condition/scrutinee first and contributes only
    the selected branch to the local trace; and
  - an omitted else contributes one exact continuing Unit-valued identity
    predecessor carrying the incoming resource/evidence/obligation state.

  Target physical order is deliberately not source semantic identity.  A target
  projection may differ only through an explicit StageContract-bound refinement
  whose changed crossings have evidence and whose other effect/resource/failure/
  authority/observable succession relations remain preserved.

  Concrete Grammar-v1 AST traversal, Located occurrence identity, branch-choice
  evidence lookup, Text/Digest/Set representation, the concrete adjacent-crossing
  search in Phil.Systems.SequentialTrace, StageContract serialization, and
  Haskell implementation correspondence remain explicit representation
  boundaries.
*)

Definition ExecutionEvent := nat.

Inductive LocalControl : Type :=
| LocalContinues
| LocalStops.

Record LocalTraceResult : Type := mkLocalTraceResult {
  localTrace : list ExecutionEvent;
  localControl : LocalControl
}.

Fixpoint sequenceLocalResults
  (results : list LocalTraceResult) : LocalTraceResult :=
  match results with
  | [] => mkLocalTraceResult [] LocalContinues
  | first :: rest =>
      match localControl first with
      | LocalStops => first
      | LocalContinues =>
          let tail := sequenceLocalResults rest in
          mkLocalTraceResult
            (localTrace first ++ localTrace tail)
            (localControl tail)
      end
  end.

Theorem stopped_local_result_suppresses_suffix :
  forall trace suffix,
    sequenceLocalResults
      (mkLocalTraceResult trace LocalStops :: suffix) =
    mkLocalTraceResult trace LocalStops.
Proof.
  reflexivity.
Qed.

Theorem continuing_local_result_prefixes_tail_in_order :
  forall trace suffix,
    sequenceLocalResults
      (mkLocalTraceResult trace LocalContinues :: suffix) =
    mkLocalTraceResult
      (trace ++ localTrace (sequenceLocalResults suffix))
      (localControl (sequenceLocalResults suffix)).
Proof.
  reflexivity.
Qed.

Definition evaluateStrictChildren := sequenceLocalResults.

Theorem strict_child_stop_suppresses_later_children :
  forall childTrace laterChildren,
    evaluateStrictChildren
      (mkLocalTraceResult childTrace LocalStops :: laterChildren) =
    mkLocalTraceResult childTrace LocalStops.
Proof.
  reflexivity.
Qed.

Theorem strict_child_continuation_preserves_left_to_right_prefix :
  forall childTrace laterChildren,
    localTrace
      (evaluateStrictChildren
        (mkLocalTraceResult childTrace LocalContinues :: laterChildren)) =
    childTrace ++ localTrace (evaluateStrictChildren laterChildren).
Proof.
  reflexivity.
Qed.

Definition executeSelectedBranch
  (condition selected : LocalTraceResult) : LocalTraceResult :=
  match localControl condition with
  | LocalStops => condition
  | LocalContinues =>
      mkLocalTraceResult
        (localTrace condition ++ localTrace selected)
        (localControl selected)
  end.

Theorem stopped_condition_suppresses_branch :
  forall conditionTrace selected,
    executeSelectedBranch
      (mkLocalTraceResult conditionTrace LocalStops)
      selected =
    mkLocalTraceResult conditionTrace LocalStops.
Proof.
  reflexivity.
Qed.

Theorem continuing_condition_precedes_selected_branch :
  forall conditionTrace selected,
    localTrace
      (executeSelectedBranch
        (mkLocalTraceResult conditionTrace LocalContinues)
        selected) =
    conditionTrace ++ localTrace selected.
Proof.
  reflexivity.
Qed.

Definition executeOneBranch
  (condition selected untaken : LocalTraceResult) : LocalTraceResult :=
  executeSelectedBranch condition selected.

Theorem untaken_branch_cannot_contribute_local_trace :
  forall condition selected firstUntaken secondUntaken,
    executeOneBranch condition selected firstUntaken =
    executeOneBranch condition selected secondUntaken.
Proof.
  reflexivity.
Qed.

Record SemanticContinuationState : Type := mkSemanticContinuationState {
  continuationResourceState : nat;
  continuationEvidenceState : nat;
  continuationObligationState : nat
}.

Inductive LocalValue : Type :=
| LocalUnit
| LocalOtherValue.

Record BranchContinuation : Type := mkBranchContinuation {
  branchContinuationState : SemanticContinuationState;
  branchContinuationValue : LocalValue;
  branchContinuationControl : LocalControl
}.

Definition omittedElseFalseContinuation
  (incoming : SemanticContinuationState) : BranchContinuation :=
  mkBranchContinuation incoming LocalUnit LocalContinues.

Theorem omitted_else_false_is_exact_identity_predecessor :
  forall incoming,
    branchContinuationState (omittedElseFalseContinuation incoming) = incoming /\
    branchContinuationValue (omittedElseFalseContinuation incoming) = LocalUnit /\
    branchContinuationControl (omittedElseFalseContinuation incoming) =
      LocalContinues.
Proof.
  intros incoming.
  repeat split; reflexivity.
Qed.

Theorem omitted_else_false_preserves_resource_evidence_obligation_state :
  forall incoming,
    continuationResourceState
      (branchContinuationState (omittedElseFalseContinuation incoming)) =
      continuationResourceState incoming /\
    continuationEvidenceState
      (branchContinuationState (omittedElseFalseContinuation incoming)) =
      continuationEvidenceState incoming /\
    continuationObligationState
      (branchContinuationState (omittedElseFalseContinuation incoming)) =
      continuationObligationState incoming.
Proof.
  intros incoming.
  repeat split; reflexivity.
Qed.

Record StageSemanticPreservation : Type := mkStageSemanticPreservation {
  stageEffectsPreserved : Prop;
  stageResourcesPreserved : Prop;
  stageFailuresPreserved : Prop;
  stageAuthorityPreserved : Prop;
  stageObservablesPreserved : Prop
}.

Definition StageSemanticPreservationValid
  (preservation : StageSemanticPreservation) : Prop :=
  stageEffectsPreserved preservation /\
  stageResourcesPreserved preservation /\
  stageFailuresPreserved preservation /\
  stageAuthorityPreserved preservation /\
  stageObservablesPreserved preservation.

Record SequentialTargetRefinement : Type := mkSequentialTargetRefinement {
  sequentialStageContractIdentityMatches : Prop;
  sequentialSourceArtifactIdentityMatches : Prop;
  sequentialTargetArtifactIdentityMatches : Prop;
  sequentialEventDomainMatchesExactly : Prop;
  sequentialTraceRelationRecorded : Prop;
  sequentialChangedCrossingsHaveEvidence : Prop;
  sequentialStageSemantics : StageSemanticPreservation
}.

Definition SequentialTargetRefinementValid
  (refinement : SequentialTargetRefinement) : Prop :=
  sequentialStageContractIdentityMatches refinement /\
  sequentialSourceArtifactIdentityMatches refinement /\
  sequentialTargetArtifactIdentityMatches refinement /\
  sequentialEventDomainMatchesExactly refinement /\
  sequentialTraceRelationRecorded refinement /\
  sequentialChangedCrossingsHaveEvidence refinement /\
  StageSemanticPreservationValid (sequentialStageSemantics refinement).

Theorem target_reordering_requires_explicit_crossing_evidence :
  forall refinement,
    SequentialTargetRefinementValid refinement ->
    sequentialChangedCrossingsHaveEvidence refinement.
Proof.
  intros refinement Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hcrossings _]]]]]].
  exact Hcrossings.
Qed.

Theorem target_reordering_preserves_effect_resource_failure_authority_observables :
  forall refinement,
    SequentialTargetRefinementValid refinement ->
    StageSemanticPreservationValid (sequentialStageSemantics refinement).
Proof.
  intros refinement Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [_ Hsemantics]]]]]].
  exact Hsemantics.
Qed.

Theorem speculative_or_untaken_event_domain_drift_rejects_refinement :
  forall refinement,
    ~ sequentialEventDomainMatchesExactly refinement ->
    ~ SequentialTargetRefinementValid refinement.
Proof.
  intros refinement Hdomain Hvalid.
  apply Hdomain.
  destruct Hvalid as [_ [_ [_ [Hexact _]]]].
  exact Hexact.
Qed.

Theorem unproved_crossing_rejects_refinement :
  forall refinement,
    ~ sequentialChangedCrossingsHaveEvidence refinement ->
    ~ SequentialTargetRefinementValid refinement.
Proof.
  intros refinement Hcrossings Hvalid.
  apply Hcrossings.
  eapply target_reordering_requires_explicit_crossing_evidence.
  exact Hvalid.
Qed.

Theorem stage_contract_identity_mismatch_rejects_refinement :
  forall refinement,
    ~ sequentialStageContractIdentityMatches refinement ->
    ~ SequentialTargetRefinementValid refinement.
Proof.
  intros refinement Hidentity Hvalid.
  apply Hidentity.
  exact (proj1 Hvalid).
Qed.
