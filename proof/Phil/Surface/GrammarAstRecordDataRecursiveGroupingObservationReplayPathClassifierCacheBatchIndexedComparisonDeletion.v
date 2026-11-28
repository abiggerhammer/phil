From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonLaws
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonAppend.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional comparison under deletion.
   Removing a single occurrence preserves prefix indices and shifts suffix
   indices by one, without deduplicating equal entries. Comparisons at
   surviving positions transport exactly, including missing suffix indices.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_comparison_delete_prefix_lookup :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry) removed suffix i,
    i < length prefix ->
    nth_error (prefix ++ suffix) i =
    nth_error (prefix ++ removed :: suffix) i.
Proof.
  intros prefix removed suffix i Hi.
  transitivity (nth_error prefix i).
  - apply nth_error_app1. exact Hi.
  - symmetry. apply nth_error_app1. exact Hi.
Qed.

Theorem phase1_surface_classifier_cache_batch_comparison_delete_suffix_lookup :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry) removed suffix j,
    nth_error (prefix ++ suffix) (length prefix + j) =
    nth_error (prefix ++ removed :: suffix) (length prefix + S j).
Proof.
  intros prefix removed suffix j.
  rewrite (phase1_surface_classifier_cache_batch_append_shifted_lookup prefix suffix j).
  rewrite (phase1_surface_classifier_cache_batch_append_shifted_lookup
    prefix (removed :: suffix) (S j)).
  reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_delete_prefix :
  forall prefix removed suffix i j,
    i < length prefix ->
    j < length prefix ->
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix) i j =
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ removed :: suffix) i j.
Proof.
  intros prefix removed suffix i j Hi Hj.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence.
  - apply phase1_surface_classifier_cache_batch_comparison_delete_prefix_lookup. exact Hi.
  - apply phase1_surface_classifier_cache_batch_comparison_delete_prefix_lookup. exact Hj.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_delete_suffix :
  forall prefix removed suffix i j,
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix)
      (length prefix + i) (length prefix + j) =
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ removed :: suffix)
      (length prefix + S i) (length prefix + S j).
Proof.
  intros prefix removed suffix i j.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence;
    apply phase1_surface_classifier_cache_batch_comparison_delete_suffix_lookup.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_delete_cross :
  forall prefix removed suffix i j,
    i < length prefix ->
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix)
      i (length prefix + j) =
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ removed :: suffix)
      i (length prefix + S j).
Proof.
  intros prefix removed suffix i j Hi.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence.
  - apply phase1_surface_classifier_cache_batch_comparison_delete_prefix_lookup. exact Hi.
  - apply phase1_surface_classifier_cache_batch_comparison_delete_suffix_lookup.
Qed.

Example phase1_surface_classifier_cache_batch_compare_at_delete_duplicate_boundary :
  forall bad survivor,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: survivor :: nil) O O = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: survivor :: nil) (S O) (S O) =
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: bad :: survivor :: nil) (S (S O)) (S (S O)) /\
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: survivor :: nil) O (S (S O)) = None.
Proof.
  intros bad survivor Hb. split.
  - apply (proj2
      (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
        (bad :: survivor :: nil) O O bad bad eq_refl eq_refl)).
    left. exact Hb.
  - split; reflexivity.
Qed.
