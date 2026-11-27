From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonLaws
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonDiagnostics.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional comparison under append.
   Appending preserves comparisons at two existing prefix positions;
   comparisons within the suffix transport by the exact prefix length.
   Cross-boundary comparison checks precisely the selected entries,
   without conflating duplicates, missing indices or invalid evidence.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_append_shifted_lookup :
  forall (prefix suffix : list Phase1SurfaceClassifierCacheEntry) j,
    nth_error (prefix ++ suffix) (length prefix + j) =
    nth_error suffix j.
Proof.
  intro prefix.
  induction prefix as [|entry rest IH]; intros suffix j.
  - reflexivity.
  - exact (IH suffix j).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_append_prefix :
  forall prefix suffix i j,
    i < length prefix ->
    j < length prefix ->
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix) i j =
    phase1_surface_classifier_cache_batch_compare_at prefix i j.
Proof.
  intros prefix suffix i j Hi Hj.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence.
  - apply nth_error_app1. exact Hi.
  - apply nth_error_app1. exact Hj.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_append_suffix :
  forall prefix suffix i j,
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix)
      (length prefix + i) (length prefix + j) =
    phase1_surface_classifier_cache_batch_compare_at suffix i j.
Proof.
  intros prefix suffix i j.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence;
    apply phase1_surface_classifier_cache_batch_append_shifted_lookup.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_append_cross :
  forall prefix suffix i j,
    i < length prefix ->
    phase1_surface_classifier_cache_batch_compare_at (prefix ++ suffix)
      i (length prefix + j) =
    match nth_error prefix i, nth_error suffix j with
    | Some lentry, Some rentry =>
      Some (phase1_surface_guarded_cache_compare (fst lentry) (fst rentry)
        (snd lentry) (snd rentry))
    | _, _ => None
    end.
Proof.
  intros prefix suffix i j Hi.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  assert (Hprefix : nth_error (prefix ++ suffix) i = nth_error prefix i).
  { apply nth_error_app1. exact Hi. }
  now rewrite Hprefix, phase1_surface_classifier_cache_batch_append_shifted_lookup.
Qed.

Example phase1_surface_classifier_cache_batch_compare_at_append_invalid_suffix_boundary :
  forall good bad,
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) O O =
      Some (Phase1CacheCompared
        (phase1_surface_replay_compare (fst good) (fst good))) /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) O (S O) = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S O) (S O) = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S O) (S (S O)) = None.
Proof.
  intros good bad Hg Hb. split.
  - exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
      (phase1_surface_guarded_cache_compare_valid
        (fst good) (fst good) (snd good) (snd good) Hg Hg)).
  - split.
    + apply (proj2
        (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
          (good :: bad :: nil) O (S O) good bad eq_refl eq_refl)).
      right. exact Hb.
    + split.
      * exact (proj2
          (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
            (good :: bad :: nil) (S O) bad eq_refl) Hb).
      * reflexivity.
Qed.
