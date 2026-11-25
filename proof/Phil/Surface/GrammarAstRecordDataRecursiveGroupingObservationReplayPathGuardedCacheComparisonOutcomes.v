From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierValueComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: exact outcome characterizations at
  the paired cache validation boundary, expressed in terms of the
  proposed values and their validation. A compared result requires
  both validations, even for coincident rejection or unequal values.
  No persistent freshness, performance, admission authority,
  production binding, grammar, TCB, G2/G4 or Phase 1 closure claim.
*)

Theorem phase1_surface_guarded_cache_compare_values_iff :
  forall left right left_cached right_cached comparison,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared comparison <->
    phase1_surface_classifier_cache_validb left left_cached = true /\
    phase1_surface_classifier_cache_validb right right_cached = true /\
    phase1_surface_compare_classifier_values left_cached right_cached =
      comparison.
Proof.
  intros left right left_cached right_cached comparison.
  unfold phase1_surface_guarded_cache_compare.
  destruct (phase1_surface_classifier_cache_validb left left_cached);
    destruct (phase1_surface_classifier_cache_validb right right_cached).
  - split.
    + intro H. injection H as Hresult.
      split; [reflexivity|].
      split; [reflexivity|exact Hresult].
    + intros [_ [_ Hresult]]. rewrite Hresult. reflexivity.
  - split.
    + intro H. discriminate H.
    + intros [_ [Hright _]]. discriminate Hright.
  - split.
    + intro H. discriminate H.
    + intros [Hleft _]. discriminate Hleft.
  - split.
    + intro H. discriminate H.
    + intros [Hleft _]. discriminate Hleft.
Qed.

Theorem phase1_surface_guarded_cache_compare_shared_iff :
  forall left right left_cached right_cached,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared Phase1ReplaySharedObservation <->
    phase1_surface_classifier_cache_validb left left_cached = true /\
    phase1_surface_classifier_cache_validb right right_cached = true /\
    exists observed,
      left_cached = Some observed /\ right_cached = Some observed.
Proof.
  intros left right left_cached right_cached.
  split.
  - intro H.
    destruct (proj1 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplaySharedObservation)
      H) as [Hl [Hr Hvalue]].
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj1 (phase1_surface_compare_classifier_values_shared_iff
      left_cached right_cached) Hvalue).
  - intros [Hl [Hr Hsame]].
    apply (proj2 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplaySharedObservation)).
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj2 (phase1_surface_compare_classifier_values_shared_iff
      left_cached right_cached) Hsame).
Qed.

Theorem phase1_surface_guarded_cache_compare_rejected_iff :
  forall left right left_cached right_cached,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared Phase1ReplayBothRejected <->
    phase1_surface_classifier_cache_validb left left_cached = true /\
    phase1_surface_classifier_cache_validb right right_cached = true /\
    left_cached = @None Phase1SurfaceRecursiveGroupingObservedRecordData /\
    right_cached = @None Phase1SurfaceRecursiveGroupingObservedRecordData.
Proof.
  intros left right left_cached right_cached.
  split.
  - intro H.
    destruct (proj1 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplayBothRejected)
      H) as [Hl [Hr Hvalue]].
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj1 (phase1_surface_compare_classifier_values_rejected_iff
      left_cached right_cached) Hvalue).
  - intros [Hl [Hr Hnone]].
    apply (proj2 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplayBothRejected)).
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj2 (phase1_surface_compare_classifier_values_rejected_iff
      left_cached right_cached) Hnone).
Qed.

Theorem phase1_surface_guarded_cache_compare_distinct_iff :
  forall left right left_cached right_cached,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared Phase1ReplayDistinctClassifiers <->
    phase1_surface_classifier_cache_validb left left_cached = true /\
    phase1_surface_classifier_cache_validb right right_cached = true /\
    left_cached <> right_cached.
Proof.
  intros left right left_cached right_cached.
  split.
  - intro H.
    destruct (proj1 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplayDistinctClassifiers)
      H) as [Hl [Hr Hvalue]].
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj1 (phase1_surface_compare_classifier_values_distinct_iff
      left_cached right_cached) Hvalue).
  - intros [Hl [Hr Hneq]].
    apply (proj2 (phase1_surface_guarded_cache_compare_values_iff
      left right left_cached right_cached Phase1ReplayDistinctClassifiers)).
    split; [exact Hl|].
    split; [exact Hr|].
    exact (proj2 (phase1_surface_compare_classifier_values_distinct_iff
      left_cached right_cached) Hneq).
Qed.
