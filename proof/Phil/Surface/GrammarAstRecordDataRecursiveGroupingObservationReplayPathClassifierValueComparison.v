From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDirectComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: compare already computed classifier
  values independently of declaration keys. The option-level laws hold
  for every value, not just the classifier image. A Some value alone
  does not certify admission of any declaration; None/None is coincident
  rejection, not admitted connectivity. No production binding, new
  admission, extraction, grammar, normalization, TCB, G2/G4 or closure.
*)

Definition phase1_surface_compare_classifier_values
  (left right : option Phase1SurfaceRecursiveGroupingObservedRecordData)
  : Phase1SurfaceReplayComparison :=
  match left, right with
  | Some l, Some r =>
      if phase1_surface_observed_record_data_eq_dec l r
      then Phase1ReplaySharedObservation
      else Phase1ReplayDistinctClassifiers
  | None, None => Phase1ReplayBothRejected
  | _, _ => Phase1ReplayDistinctClassifiers
  end.

Theorem phase1_surface_compare_classifier_values_shared_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right =
      Phase1ReplaySharedObservation <->
    exists observed, left = Some observed /\ right = Some observed.
Proof.
  intros [l|] [r|]; unfold phase1_surface_compare_classifier_values.
  - destruct (phase1_surface_observed_record_data_eq_dec l r)
      as [Hequal|Hneq].
    + subst r. split.
      * intro H. exists l. split; reflexivity.
      * intro H. reflexivity.
    + split.
      * intro H. discriminate H.
      * intros [observed [Hl Hr]]. exfalso. apply Hneq. congruence.
  - split.
    + intro H. discriminate H.
    + intros [observed [Hl Hr]]. discriminate Hr.
  - split.
    + intro H. discriminate H.
    + intros [observed [Hl Hr]]. discriminate Hl.
  - split.
    + intro H. discriminate H.
    + intros [observed [Hl Hr]]. discriminate Hl.
Qed.

Theorem phase1_surface_compare_classifier_values_rejected_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right =
      Phase1ReplayBothRejected <-> left = None /\ right = None.
Proof.
  intros [l|] [r|]; unfold phase1_surface_compare_classifier_values.
  - destruct (phase1_surface_observed_record_data_eq_dec l r);
      split.
    + intro H. discriminate H.
    + intros [Hl Hr]. discriminate Hl.
    + intro H. discriminate H.
    + intros [Hl Hr]. discriminate Hl.
  - split.
    + intro H. discriminate H.
    + intros [Hl Hr]. discriminate Hl.
  - split.
    + intro H. discriminate H.
    + intros [Hl Hr]. discriminate Hr.
  - split.
    + intro H. split; reflexivity.
    + intro H. reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_values_distinct_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right =
      Phase1ReplayDistinctClassifiers <-> left <> right.
Proof.
  intros [l|] [r|]; unfold phase1_surface_compare_classifier_values.
  - destruct (phase1_surface_observed_record_data_eq_dec l r)
      as [Hequal|Hneq].
    + subst r. split.
      * intro H. discriminate H.
      * intro H. exfalso. apply H. reflexivity.
    + split.
      * intros H Hequal. apply Hneq. congruence.
      * intro H. reflexivity.
  - split.
    + intros H Hequal. discriminate Hequal.
    + intro H. reflexivity.
  - split.
    + intros H Hequal. discriminate Hequal.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H. exfalso. apply H. reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_values_direct :
  forall left right,
    phase1_surface_compare_classifier_values
      (phase1_surface_normalized_observation left)
      (phase1_surface_normalized_observation right) =
    phase1_surface_replay_compare_direct left right.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_values_replay :
  forall left right,
    phase1_surface_compare_classifier_values
      (phase1_surface_normalized_observation left)
      (phase1_surface_normalized_observation right) =
    phase1_surface_replay_compare left right.
Proof.
  intros left right.
  rewrite phase1_surface_compare_classifier_values_direct.
  apply phase1_surface_replay_compare_direct_agrees.
Qed.
