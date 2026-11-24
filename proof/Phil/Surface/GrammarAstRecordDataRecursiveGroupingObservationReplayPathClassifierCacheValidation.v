From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierValueComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierValueRows.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: validate a proposed cached option
  against the declaration's recomputed classifier. Acceptance is exact
  value equality, including None; it is not declaration admission.
  Validated values may substitute in either comparison position for
  all declaration probes. No cache freshness or persistent authority,
  grammar, normalization, extraction, production binding, TCB, G2/G4
  or Phase 1 closure claim.
*)

Definition phase1_surface_classifier_cache_validb
  (declaration : Phase1SurfaceDeclarationSpine)
  (cached : option Phase1SurfaceRecursiveGroupingObservedRecordData)
  : bool :=
  match phase1_surface_compare_classifier_values cached
          (phase1_surface_normalized_observation declaration) with
  | Phase1ReplayDistinctClassifiers => false
  | _ => true
  end.

Theorem phase1_surface_classifier_cache_validb_iff :
  forall declaration cached,
    phase1_surface_classifier_cache_validb declaration cached = true <->
    cached = phase1_surface_normalized_observation declaration.
Proof.
  intros declaration cached.
  unfold phase1_surface_classifier_cache_validb.
  destruct (phase1_surface_compare_classifier_values cached
    (phase1_surface_normalized_observation declaration)) eqn:Hcompare.
  - split.
    + intro H.
      apply (proj1 (phase1_surface_compare_classifier_values_not_distinct_iff
        cached (phase1_surface_normalized_observation declaration))).
      rewrite Hcompare. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H.
      apply (proj1 (phase1_surface_compare_classifier_values_not_distinct_iff
        cached (phase1_surface_normalized_observation declaration))).
      rewrite Hcompare. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro Hequal. exfalso.
      exact ((proj1 (phase1_surface_compare_classifier_values_distinct_iff
        cached (phase1_surface_normalized_observation declaration))
        Hcompare) Hequal).
Qed.

Theorem phase1_surface_classifier_cache_validb_rows_iff :
  forall declaration cached,
    phase1_surface_classifier_cache_validb declaration cached = true <->
    (forall probe,
      phase1_surface_compare_classifier_values cached
        (phase1_surface_normalized_observation probe) =
      phase1_surface_replay_compare declaration probe).
Proof.
  intros declaration cached. split.
  - intros Hvalid probe.
    apply (proj1 (phase1_surface_classifier_cache_validb_iff
      declaration cached)) in Hvalid.
    rewrite Hvalid.
    apply phase1_surface_compare_classifier_values_replay.
  - intro Hrows.
    apply (proj2 (phase1_surface_classifier_cache_validb_iff
      declaration cached)).
    specialize (Hrows declaration).
    rewrite <- phase1_surface_compare_classifier_values_replay in Hrows.
    apply (proj1 (phase1_surface_compare_classifier_values_right_self_probe_iff
      cached (phase1_surface_normalized_observation declaration))).
    exact Hrows.
Qed.

Theorem phase1_surface_classifier_cache_validb_columns_iff :
  forall declaration cached,
    phase1_surface_classifier_cache_validb declaration cached = true <->
    (forall probe,
      phase1_surface_compare_classifier_values
        (phase1_surface_normalized_observation probe) cached =
      phase1_surface_replay_compare probe declaration).
Proof.
  intros declaration cached. split.
  - intros Hvalid probe.
    apply (proj1 (phase1_surface_classifier_cache_validb_iff
      declaration cached)) in Hvalid.
    rewrite Hvalid.
    apply phase1_surface_compare_classifier_values_replay.
  - intro Hcolumns.
    apply (proj2 (phase1_surface_classifier_cache_validb_iff
      declaration cached)).
    specialize (Hcolumns declaration).
    rewrite <- phase1_surface_compare_classifier_values_replay in Hcolumns.
    symmetry.
    apply (proj1 (phase1_surface_compare_classifier_values_left_self_probe_iff
      (phase1_surface_normalized_observation declaration) cached)).
    exact Hcolumns.
Qed.

Theorem phase1_surface_classifier_cache_validb_none_iff :
  forall declaration,
    phase1_surface_classifier_cache_validb declaration None = true <->
    phase1_surface_normalized_observation declaration = None.
Proof.
  intro declaration.
  rewrite phase1_surface_classifier_cache_validb_iff.
  split; intro H; symmetry; exact H.
Qed.

Theorem phase1_surface_classifier_cache_validb_some_iff :
  forall declaration observed,
    phase1_surface_classifier_cache_validb declaration (Some observed) = true <->
    phase1_surface_normalized_observation declaration = Some observed.
Proof.
  intros declaration observed.
  rewrite phase1_surface_classifier_cache_validb_iff.
  split; intro H; symmetry; exact H.
Qed.
