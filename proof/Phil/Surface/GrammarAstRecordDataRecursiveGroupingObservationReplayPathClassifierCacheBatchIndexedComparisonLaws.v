From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparisonLaws
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional comparison laws.
   Only the selected entries matter. Shared observations and coincident
   rejection compose separately through the same present middle index.
   Successful selected comparison does not imply whole-batch validity.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_compare_at_lookup_congruence :
  forall entries entries' i j i' j',
    nth_error entries i = nth_error entries' i' ->
    nth_error entries j = nth_error entries' j' ->
    phase1_surface_classifier_cache_batch_compare_at entries i j =
    phase1_surface_classifier_cache_batch_compare_at entries' i' j'.
Proof.
  intros entries entries' i j i' j' Hl Hr.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  now rewrite Hl, Hr.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_symmetric :
  forall entries i j,
    phase1_surface_classifier_cache_batch_compare_at entries i j =
    phase1_surface_classifier_cache_batch_compare_at entries j i.
Proof.
  intros entries i j.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  destruct (nth_error entries i) as [left|];
    destruct (nth_error entries j) as [right|]; try reflexivity.
  exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
    (phase1_surface_guarded_cache_compare_symmetric
      (fst left) (fst right) (snd left) (snd right))).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_shared_transitive :
  forall entries i j k,
    phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some (Phase1CacheCompared Phase1ReplaySharedObservation) ->
    phase1_surface_classifier_cache_batch_compare_at entries j k =
      Some (Phase1CacheCompared Phase1ReplaySharedObservation) ->
    phase1_surface_classifier_cache_batch_compare_at entries i k =
      Some (Phase1CacheCompared Phase1ReplaySharedObservation).
Proof.
  intros entries i j k Hfirst Hsecond.
  unfold phase1_surface_classifier_cache_batch_compare_at in *.
  destruct (nth_error entries i) as [left|]; try discriminate Hfirst.
  destruct (nth_error entries j) as [middle|]; try discriminate Hfirst.
  destruct (nth_error entries k) as [right|]; try discriminate Hsecond.
  injection Hfirst as Hlm.
  injection Hsecond as Hmr.
  exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
    (phase1_surface_guarded_cache_compare_shared_transitive
      (fst left) (fst middle) (fst right) (snd left) (snd middle)
      (snd middle) (snd right) Hlm Hmr)).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_rejected_transitive :
  forall entries i j k,
    phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some (Phase1CacheCompared Phase1ReplayBothRejected) ->
    phase1_surface_classifier_cache_batch_compare_at entries j k =
      Some (Phase1CacheCompared Phase1ReplayBothRejected) ->
    phase1_surface_classifier_cache_batch_compare_at entries i k =
      Some (Phase1CacheCompared Phase1ReplayBothRejected).
Proof.
  intros entries i j k Hfirst Hsecond.
  unfold phase1_surface_classifier_cache_batch_compare_at in *.
  destruct (nth_error entries i) as [left|]; try discriminate Hfirst.
  destruct (nth_error entries j) as [middle|]; try discriminate Hfirst.
  destruct (nth_error entries k) as [right|]; try discriminate Hsecond.
  injection Hfirst as Hlm.
  injection Hsecond as Hmr.
  exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
    (phase1_surface_guarded_cache_compare_rejected_transitive
      (fst left) (fst middle) (fst right) (snd left) (snd middle)
      (snd middle) (snd right) Hlm Hmr)).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_shared_rejected_incompatible :
  forall entries i j k,
    phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some (Phase1CacheCompared Phase1ReplaySharedObservation) ->
    phase1_surface_classifier_cache_batch_compare_at entries j k =
      Some (Phase1CacheCompared Phase1ReplayBothRejected) ->
    False.
Proof.
  intros entries i j k Hfirst Hsecond.
  unfold phase1_surface_classifier_cache_batch_compare_at in *.
  destruct (nth_error entries i) as [left|]; try discriminate Hfirst.
  destruct (nth_error entries j) as [middle|]; try discriminate Hfirst.
  destruct (nth_error entries k) as [right|]; try discriminate Hsecond.
  injection Hfirst as Hlm.
  injection Hsecond as Hmr.
  exact (phase1_surface_guarded_cache_compare_shared_rejected_incompatible
    (fst left) (fst middle) (fst right) (snd left) (snd middle)
    (snd middle) (snd right) Hlm Hmr).
Qed.

Example phase1_surface_classifier_cache_batch_compare_at_invalid_unselected_duplicate :
  forall declaration good bad,
    phase1_surface_classifier_cache_validb declaration good = true ->
    phase1_surface_classifier_cache_validb declaration bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      ((declaration, good) :: (declaration, bad) :: nil) O O =
      Some (Phase1CacheCompared
        (phase1_surface_replay_compare declaration declaration)) /\
    phase1_surface_classifier_cache_batch_compare_at
      ((declaration, good) :: (declaration, bad) :: nil) O (S O) =
      Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_validb
      ((declaration, good) :: (declaration, bad) :: nil) = false.
Proof.
  intros declaration good bad Hgood Hbad.
  split.
  - change (Some (phase1_surface_guarded_cache_compare
      declaration declaration good good) =
      Some (Phase1CacheCompared
        (phase1_surface_replay_compare declaration declaration))).
    exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
      (phase1_surface_guarded_cache_compare_valid
        declaration declaration good good Hgood Hgood)).
  - split.
    + change (Some (phase1_surface_guarded_cache_compare
        declaration declaration good bad) = Some Phase1CacheInvalid).
      assert (Hinvalid : phase1_surface_guarded_cache_compare
        declaration declaration good bad = Phase1CacheInvalid).
      { apply (proj2 (phase1_surface_guarded_cache_compare_invalid_iff
          declaration declaration good bad)).
        right. exact Hbad. }
      exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison) Hinvalid).
    + exact (phase1_surface_classifier_cache_batch_invalid_duplicate
        declaration good bad Hgood Hbad).
Qed.
