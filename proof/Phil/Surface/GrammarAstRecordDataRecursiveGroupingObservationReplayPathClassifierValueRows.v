From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierValueComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: extensionality of comparison
  rows and columns over already computed classifier values. Either
  endpoint supplies a sufficient self-probe. Coincident rejection is
  classifier equality, not admitted connectivity. Arbitrary successful
  values confer no declaration admission. No grammar, normalization,
  extraction, production binding, TCB, G2/G4 or closure claim.
*)

Theorem phase1_surface_compare_classifier_values_not_distinct_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right <>
      Phase1ReplayDistinctClassifiers <-> left = right.
Proof.
  intros left right. split.
  - intro Hnot.
    destruct (phase1_surface_compare_classifier_values left right) eqn:Hcompare.
    + destruct (proj1 (phase1_surface_compare_classifier_values_shared_iff
        left right) Hcompare) as [observed [Hl Hr]].
      congruence.
    + destruct (proj1 (phase1_surface_compare_classifier_values_rejected_iff
        left right) Hcompare) as [Hl Hr].
      congruence.
    + exfalso. apply Hnot. reflexivity.
  - intros Hequal Hcompare.
    exact ((proj1 (phase1_surface_compare_classifier_values_distinct_iff
      left right) Hcompare) Hequal).
Qed.

Theorem phase1_surface_compare_classifier_values_left_self_probe_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right =
      phase1_surface_compare_classifier_values left left <->
    left = right.
Proof.
  intros left right. split.
  - intro Hprobe.
    apply (proj1 (phase1_surface_compare_classifier_values_not_distinct_iff
      left right)).
    intro Hdistinct.
    assert (Hdiag : phase1_surface_compare_classifier_values left left =
        Phase1ReplayDistinctClassifiers).
    { rewrite <- Hprobe. exact Hdistinct. }
    exact ((proj1 (phase1_surface_compare_classifier_values_distinct_iff
      left left) Hdiag) eq_refl).
  - intro Hequal. subst right. reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_values_right_self_probe_iff :
  forall left right,
    phase1_surface_compare_classifier_values left right =
      phase1_surface_compare_classifier_values right right <->
    left = right.
Proof.
  intros left right. split.
  - intro Hprobe.
    apply (proj1 (phase1_surface_compare_classifier_values_not_distinct_iff
      left right)).
    intro Hdistinct.
    assert (Hdiag : phase1_surface_compare_classifier_values right right =
        Phase1ReplayDistinctClassifiers).
    { rewrite <- Hprobe. exact Hdistinct. }
    exact ((proj1 (phase1_surface_compare_classifier_values_distinct_iff
      right right) Hdiag) eq_refl).
  - intro Hequal. subst right. reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_value_rows_equal_iff :
  forall left right,
    (forall probe,
      phase1_surface_compare_classifier_values left probe =
      phase1_surface_compare_classifier_values right probe) <->
    left = right.
Proof.
  intros left right. split.
  - intro Hrows.
    apply (proj1 (phase1_surface_compare_classifier_values_right_self_probe_iff
      left right)).
    exact (Hrows right).
  - intro Hequal. subst right. intro probe. reflexivity.
Qed.

Theorem phase1_surface_compare_classifier_value_columns_equal_iff :
  forall left right,
    (forall probe,
      phase1_surface_compare_classifier_values probe left =
      phase1_surface_compare_classifier_values probe right) <->
    left = right.
Proof.
  intros left right. split.
  - intro Hcolumns.
    apply (proj1 (phase1_surface_compare_classifier_values_left_self_probe_iff
      left right)).
    symmetry. exact (Hcolumns left).
  - intro Hequal. subst right. intro probe. reflexivity.
Qed.
