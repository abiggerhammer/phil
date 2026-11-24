From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: total comparison laws.
   Coincident rejection is not admitted connectivity. No grammar,
   normalization, production binding, TCB, G2/G4 or closure claim. *)

Theorem phase1_surface_replay_comparison_classifier_congruence :
  forall left left' right right',
    phase1_surface_normalized_observation left =
      phase1_surface_normalized_observation left' ->
    phase1_surface_normalized_observation right =
      phase1_surface_normalized_observation right' ->
    phase1_surface_replay_compare left right =
      phase1_surface_replay_compare left' right'.
Proof.
  intros left left' right right' Hleft Hright.
  destruct (phase1_surface_replay_compare left right) eqn:Hcompare;
    symmetry.
  - apply (proj2 (phase1_surface_replay_comparison_shared_iff left' right')).
    destruct (proj1 (phase1_surface_replay_comparison_shared_iff
      left right) Hcompare) as [observed [Hl Hr]].
    exists observed. split.
    + rewrite <- Hleft. exact Hl.
    + rewrite <- Hright. exact Hr.
  - apply (proj2 (phase1_surface_replay_comparison_rejected_iff left' right')).
    destruct (proj1 (phase1_surface_replay_comparison_rejected_iff
      left right) Hcompare) as [Hl Hr].
    split.
    + rewrite <- Hleft. exact Hl.
    + rewrite <- Hright. exact Hr.
  - apply (proj2 (phase1_surface_replay_comparison_distinct_iff left' right')).
    pose proof (proj1 (phase1_surface_replay_comparison_distinct_iff
      left right) Hcompare) as Hneq.
    rewrite <- Hleft, <- Hright. exact Hneq.
Qed.

Theorem phase1_surface_replay_comparison_symmetric :
  forall left right,
    phase1_surface_replay_compare left right =
    phase1_surface_replay_compare right left.
Proof.
  intros left right.
  destruct (phase1_surface_replay_compare left right) eqn:Hcompare;
    symmetry.
  - apply (proj2 (phase1_surface_replay_comparison_shared_iff right left)).
    destruct (proj1 (phase1_surface_replay_comparison_shared_iff
      left right) Hcompare) as [observed [Hl Hr]].
    exists observed. split; assumption.
  - apply (proj2 (phase1_surface_replay_comparison_rejected_iff right left)).
    destruct (proj1 (phase1_surface_replay_comparison_rejected_iff
      left right) Hcompare) as [Hl Hr].
    split; assumption.
  - apply (proj2 (phase1_surface_replay_comparison_distinct_iff right left)).
    pose proof (proj1 (phase1_surface_replay_comparison_distinct_iff
      left right) Hcompare) as Hneq.
    intro Hequal. apply Hneq. symmetry. exact Hequal.
Qed.

Theorem phase1_surface_replay_comparison_shared_transitive :
  forall left middle right,
    phase1_surface_replay_compare left middle = Phase1ReplaySharedObservation ->
    phase1_surface_replay_compare middle right = Phase1ReplaySharedObservation ->
    phase1_surface_replay_compare left right = Phase1ReplaySharedObservation.
Proof.
  intros left middle right Hfirst Hsecond.
  destruct (proj1 (phase1_surface_replay_comparison_shared_iff
    left middle) Hfirst) as [o1 [Hl Hm]].
  destruct (proj1 (phase1_surface_replay_comparison_shared_iff
    middle right) Hsecond) as [o2 [Hm' Hr]].
  apply (proj2 (phase1_surface_replay_comparison_shared_iff left right)).
  exists o1. split.
  - exact Hl.
  - assert (Hequal : o1 = o2) by congruence.
    rewrite Hequal. exact Hr.
Qed.

Theorem phase1_surface_replay_comparison_rejected_transitive :
  forall left middle right,
    phase1_surface_replay_compare left middle = Phase1ReplayBothRejected ->
    phase1_surface_replay_compare middle right = Phase1ReplayBothRejected ->
    phase1_surface_replay_compare left right = Phase1ReplayBothRejected.
Proof.
  intros left middle right Hfirst Hsecond.
  destruct (proj1 (phase1_surface_replay_comparison_rejected_iff
    left middle) Hfirst) as [Hl Hm].
  destruct (proj1 (phase1_surface_replay_comparison_rejected_iff
    middle right) Hsecond) as [Hm' Hr].
  apply (proj2 (phase1_surface_replay_comparison_rejected_iff left right)).
  split; assumption.
Qed.

Theorem phase1_surface_replay_comparison_shared_rejected_incompatible :
  forall left middle right,
    phase1_surface_replay_compare left middle = Phase1ReplaySharedObservation ->
    phase1_surface_replay_compare middle right = Phase1ReplayBothRejected ->
    False.
Proof.
  intros left middle right Hfirst Hsecond.
  destruct (proj1 (phase1_surface_replay_comparison_shared_iff
    left middle) Hfirst) as [observed [Hl Hm]].
  destruct (proj1 (phase1_surface_replay_comparison_rejected_iff
    middle right) Hsecond) as [Hm' Hr].
  rewrite Hm in Hm'. discriminate Hm'.
Qed.
