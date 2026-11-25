From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparisonLaws
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: guarded comparison composition.
  Independently proposed middle caches need not be assumed equal:
  successful comparisons establish their equality through exact
  validation against the same declaration. Shared observations compose;
  coincident rejection composes separately and cannot be mixed with
  shared observations. Invalid evidence remains a separate outcome.
  No persistent freshness, performance, admission authority, production
  binding, grammar, TCB, G2/G4 or Phase 1 closure claim.
*)

Theorem phase1_surface_guarded_cache_compare_symmetric :
  forall left right left_cached right_cached,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
    phase1_surface_guarded_cache_compare right left right_cached left_cached.
Proof.
  intros left right left_cached right_cached.
  destruct (phase1_surface_classifier_cache_validb left left_cached) eqn:Hl;
    destruct (phase1_surface_classifier_cache_validb right right_cached) eqn:Hr.
  - rewrite (phase1_surface_guarded_cache_compare_valid
      left right left_cached right_cached Hl Hr).
    rewrite (phase1_surface_guarded_cache_compare_valid
      right left right_cached left_cached Hr Hl).
    f_equal.
    apply phase1_surface_replay_comparison_symmetric.
  - unfold phase1_surface_guarded_cache_compare.
    rewrite Hl, Hr. reflexivity.
  - unfold phase1_surface_guarded_cache_compare.
    rewrite Hl, Hr. reflexivity.
  - unfold phase1_surface_guarded_cache_compare.
    rewrite Hl, Hr. reflexivity.
Qed.

Theorem phase1_surface_guarded_cache_compare_middle_agrees :
  forall left middle right left_cached middle_cached1 middle_cached2
    right_cached first second,
    phase1_surface_guarded_cache_compare left middle left_cached middle_cached1 =
      Phase1CacheCompared first ->
    phase1_surface_guarded_cache_compare middle right middle_cached2 right_cached =
      Phase1CacheCompared second ->
    middle_cached1 = middle_cached2.
Proof.
  intros left middle right left_cached middle_cached1 middle_cached2
    right_cached first second Hfirst Hsecond.
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    left middle left_cached middle_cached1 first) Hfirst) as [_ [Hm1 _]].
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    middle right middle_cached2 right_cached second) Hsecond) as [Hm2 _].
  transitivity (phase1_surface_normalized_observation middle).
  - exact Hm1.
  - symmetry. exact Hm2.
Qed.

Theorem phase1_surface_guarded_cache_compare_shared_transitive :
  forall left middle right left_cached middle_cached1 middle_cached2 right_cached,
    phase1_surface_guarded_cache_compare left middle left_cached middle_cached1 =
      Phase1CacheCompared Phase1ReplaySharedObservation ->
    phase1_surface_guarded_cache_compare middle right middle_cached2 right_cached =
      Phase1CacheCompared Phase1ReplaySharedObservation ->
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared Phase1ReplaySharedObservation.
Proof.
  intros left middle right left_cached middle_cached1 middle_cached2 right_cached
    Hfirst Hsecond.
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    left middle left_cached middle_cached1 Phase1ReplaySharedObservation)
    Hfirst) as [Hl [_ Hlm]].
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    middle right middle_cached2 right_cached Phase1ReplaySharedObservation)
    Hsecond) as [_ [Hr Hmr]].
  apply (proj2 (phase1_surface_guarded_cache_compare_compared_iff
    left right left_cached right_cached Phase1ReplaySharedObservation)).
  split; [exact Hl|].
  split; [exact Hr|].
  symmetry.
  apply (phase1_surface_replay_comparison_shared_transitive left middle right).
  - symmetry. exact Hlm.
  - symmetry. exact Hmr.
Qed.

Theorem phase1_surface_guarded_cache_compare_rejected_transitive :
  forall left middle right left_cached middle_cached1 middle_cached2 right_cached,
    phase1_surface_guarded_cache_compare left middle left_cached middle_cached1 =
      Phase1CacheCompared Phase1ReplayBothRejected ->
    phase1_surface_guarded_cache_compare middle right middle_cached2 right_cached =
      Phase1CacheCompared Phase1ReplayBothRejected ->
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared Phase1ReplayBothRejected.
Proof.
  intros left middle right left_cached middle_cached1 middle_cached2 right_cached
    Hfirst Hsecond.
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    left middle left_cached middle_cached1 Phase1ReplayBothRejected)
    Hfirst) as [Hl [_ Hlm]].
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    middle right middle_cached2 right_cached Phase1ReplayBothRejected)
    Hsecond) as [_ [Hr Hmr]].
  apply (proj2 (phase1_surface_guarded_cache_compare_compared_iff
    left right left_cached right_cached Phase1ReplayBothRejected)).
  split; [exact Hl|].
  split; [exact Hr|].
  symmetry.
  apply (phase1_surface_replay_comparison_rejected_transitive left middle right).
  - symmetry. exact Hlm.
  - symmetry. exact Hmr.
Qed.

Theorem phase1_surface_guarded_cache_compare_shared_rejected_incompatible :
  forall left middle right left_cached middle_cached1 middle_cached2 right_cached,
    phase1_surface_guarded_cache_compare left middle left_cached middle_cached1 =
      Phase1CacheCompared Phase1ReplaySharedObservation ->
    phase1_surface_guarded_cache_compare middle right middle_cached2 right_cached =
      Phase1CacheCompared Phase1ReplayBothRejected ->
    False.
Proof.
  intros left middle right left_cached middle_cached1 middle_cached2 right_cached
    Hfirst Hsecond.
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    left middle left_cached middle_cached1 Phase1ReplaySharedObservation)
    Hfirst) as [_ [_ Hlm]].
  destruct (proj1 (phase1_surface_guarded_cache_compare_compared_iff
    middle right middle_cached2 right_cached Phase1ReplayBothRejected)
    Hsecond) as [_ [_ Hmr]].
  apply (phase1_surface_replay_comparison_shared_rejected_incompatible
    left middle right).
  - symmetry. exact Hlm.
  - symmetry. exact Hmr.
Qed.
