From Stdlib Require Import Bool.Bool Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierExtensionality
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathTwoProbeClassifier.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: a total, three-way comparison
  of replay observations. A shared admitted observation is distinct
  from coincident rejection; different classifiers are a third outcome.
  No new admission, production binding, grammar, normalization, TCB,
  G2/G4, or Phase 1 closure claim.
*)

Inductive Phase1SurfaceReplayComparison : Type :=
| Phase1ReplaySharedObservation
| Phase1ReplayBothRejected
| Phase1ReplayDistinctClassifiers.

Definition phase1_surface_replay_compare
  (left right : Phase1SurfaceDeclarationSpine) :
  Phase1SurfaceReplayComparison :=
  if phase1_surface_replay_path_connectedb left right
  then Phase1ReplaySharedObservation
  else if phase1_surface_replay_two_probe_equalb left right
       then Phase1ReplayBothRejected
       else Phase1ReplayDistinctClassifiers.

Theorem phase1_surface_replay_comparison_shared_iff :
  forall left right,
    phase1_surface_replay_compare left right =
      Phase1ReplaySharedObservation <->
    exists observed,
      phase1_surface_normalized_observation left = Some observed /\
      phase1_surface_normalized_observation right = Some observed.
Proof.
  intros left right.
  split.
  - intro Hcomparison.
    unfold phase1_surface_replay_compare in Hcomparison.
    destruct (phase1_surface_replay_path_connectedb left right) eqn:Hedge.
    + exact (proj1 (phase1_surface_replay_path_connectedb_iff_same_success
        left right) Hedge).
    + destruct (phase1_surface_replay_two_probe_equalb left right);
        discriminate Hcomparison.
  - intro Hsame.
    pose proof (proj2 (phase1_surface_replay_path_connectedb_iff_same_success
      left right) Hsame) as Hedge.
    unfold phase1_surface_replay_compare.
    rewrite Hedge.
    reflexivity.
Qed.

Theorem phase1_surface_replay_comparison_rejected_iff :
  forall left right,
    phase1_surface_replay_compare left right =
      Phase1ReplayBothRejected <->
    phase1_surface_normalized_observation left = None /\
    phase1_surface_normalized_observation right = None.
Proof.
  intros left right.
  split.
  - intro Hcomparison.
    unfold phase1_surface_replay_compare in Hcomparison.
    destruct (phase1_surface_replay_path_connectedb left right) eqn:Hedge.
    + discriminate Hcomparison.
    + destruct (phase1_surface_replay_two_probe_equalb left right) eqn:Htest.
      * apply (proj1 (phase1_surface_replay_equal_disconnected_rows_iff_rejected
          left right)).
        split.
        -- exact (proj1 (phase1_surface_replay_two_probe_equalb_iff_rows
             left right) Htest).
        -- exact Hedge.
      * discriminate Hcomparison.
  - intro Hrejected.
    destruct (proj2 (phase1_surface_replay_equal_disconnected_rows_iff_rejected
      left right) Hrejected) as [Hrows Hedge].
    pose proof (proj2 (phase1_surface_replay_two_probe_equalb_iff_rows
      left right) Hrows) as Htest.
    unfold phase1_surface_replay_compare.
    rewrite Hedge, Htest.
    reflexivity.
Qed.

Theorem phase1_surface_replay_comparison_distinct_iff :
  forall left right,
    phase1_surface_replay_compare left right =
      Phase1ReplayDistinctClassifiers <->
    phase1_surface_normalized_observation left <>
    phase1_surface_normalized_observation right.
Proof.
  intros left right.
  split.
  - intros Hcomparison Hequal.
    pose proof (proj2 (phase1_surface_replay_two_probe_equalb_iff_classifier
      left right) Hequal) as Htest.
    unfold phase1_surface_replay_compare in Hcomparison.
    rewrite Htest in Hcomparison.
    destruct (phase1_surface_replay_path_connectedb left right);
      discriminate Hcomparison.
  - intro Hneq.
    unfold phase1_surface_replay_compare.
    destruct (phase1_surface_replay_path_connectedb left right) eqn:Hedge.
    + exfalso.
      apply Hneq.
      destruct (proj1 (phase1_surface_replay_path_connectedb_iff_same_success
        left right) Hedge) as [observed [Hleft Hright]].
      rewrite Hleft, Hright.
      reflexivity.
    + destruct (phase1_surface_replay_two_probe_equalb left right) eqn:Htest.
      * exfalso.
        apply Hneq.
        exact (proj1 (phase1_surface_replay_two_probe_equalb_iff_classifier
          left right) Htest).
      * reflexivity.
Qed.

Example phase1_surface_replay_comparison_success_self :
  forall declaration observed,
    phase1_surface_normalized_observation declaration = Some observed ->
    phase1_surface_replay_compare declaration declaration =
      Phase1ReplaySharedObservation.
Proof.
  intros declaration observed Hsome.
  apply (proj2 (phase1_surface_replay_comparison_shared_iff
    declaration declaration)).
  exists observed.
  split; exact Hsome.
Qed.

Example phase1_surface_replay_comparison_malformed_rejected :
  forall rejected,
    phase1_surface_normalized_observation rejected = None ->
    phase1_surface_replay_compare
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      rejected = Phase1ReplayBothRejected.
Proof.
  intros rejected Hrejected.
  destruct (phase1_surface_replay_two_probe_malformed_rejected_collision
    rejected Hrejected) as [Htest Hedge].
  unfold phase1_surface_replay_compare.
  rewrite Hedge, Htest.
  reflexivity.
Qed.
