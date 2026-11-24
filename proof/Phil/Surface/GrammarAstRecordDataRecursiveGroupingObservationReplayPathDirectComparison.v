From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: direct comparison of the two
  option-valued observation classifiers, with one comparison of the
  successful observations. Prove pointwise agreement with the existing
  replay/path and two-probe comparison. No new admission, extraction,
  production binding, grammar, normalization, TCB, G2/G4 or closure claim.
*)

Definition phase1_surface_replay_compare_direct
  (left right : Phase1SurfaceDeclarationSpine) :
  Phase1SurfaceReplayComparison :=
  match phase1_surface_normalized_observation left,
        phase1_surface_normalized_observation right with
  | Some l, Some r =>
      if phase1_surface_observed_record_data_eq_dec l r
      then Phase1ReplaySharedObservation
      else Phase1ReplayDistinctClassifiers
  | None, None => Phase1ReplayBothRejected
  | _, _ => Phase1ReplayDistinctClassifiers
  end.

Theorem phase1_surface_replay_compare_direct_agrees :
  forall left right,
    phase1_surface_replay_compare_direct left right =
    phase1_surface_replay_compare left right.
Proof.
  intros left right.
  unfold phase1_surface_replay_compare_direct.
  destruct (phase1_surface_normalized_observation left)
    as [l|] eqn:Hleft;
  destruct (phase1_surface_normalized_observation right)
    as [r|] eqn:Hright;
    symmetry.
  - destruct (phase1_surface_observed_record_data_eq_dec l r)
      as [Hequal|Hneq].
    + apply (proj2 (phase1_surface_replay_comparison_shared_iff left right)).
      exists l. split.
      * exact Hleft.
      * rewrite Hequal. exact Hright.
    + apply (proj2 (phase1_surface_replay_comparison_distinct_iff left right)).
      intro Hsame.
      rewrite Hleft, Hright in Hsame.
      injection Hsame as Hobs.
      exact (Hneq Hobs).
  - apply (proj2 (phase1_surface_replay_comparison_distinct_iff left right)).
    rewrite Hleft, Hright. discriminate.
  - apply (proj2 (phase1_surface_replay_comparison_distinct_iff left right)).
    rewrite Hleft, Hright. discriminate.
  - apply (proj2 (phase1_surface_replay_comparison_rejected_iff left right)).
    split; assumption.
Qed.

Example phase1_surface_replay_compare_direct_success_self :
  forall declaration observed,
    phase1_surface_normalized_observation declaration = Some observed ->
    phase1_surface_replay_compare_direct declaration declaration =
      Phase1ReplaySharedObservation.
Proof.
  intros declaration observed Hsome.
  unfold phase1_surface_replay_compare_direct.
  rewrite Hsome.
  destruct (phase1_surface_observed_record_data_eq_dec observed observed)
    as [Hequal|Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Example phase1_surface_replay_compare_direct_rejected_pair :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_normalized_observation right = None ->
    phase1_surface_replay_compare_direct left right =
      Phase1ReplayBothRejected.
Proof.
  intros left right Hleft Hright.
  unfold phase1_surface_replay_compare_direct.
  rewrite Hleft, Hright. reflexivity.
Qed.

Example phase1_surface_replay_compare_direct_mixed_pair :
  forall left right observed,
    phase1_surface_normalized_observation left = Some observed ->
    phase1_surface_normalized_observation right = None ->
    phase1_surface_replay_compare_direct left right =
      Phase1ReplayDistinctClassifiers.
Proof.
  intros left right observed Hleft Hright.
  unfold phase1_surface_replay_compare_direct.
  rewrite Hleft, Hright. reflexivity.
Qed.
