From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: diagonal comparison diagnostics.
   An invalid diagonal has a present invalid occurrence, never an absent
   index. All diagonals exclude invalid evidence exactly when the batch
   validates. The first-invalid diagnostic is the invalid diagonal with
   a valid preceding prefix. No persistent freshness, performance,
   admission authority, production binding, grammar, TCB, G2/G4 or
   Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff :
  forall entries index entry,
    nth_error entries index = Some entry ->
    (phase1_surface_classifier_cache_batch_compare_at entries index index =
      Some Phase1CacheInvalid <->
     phase1_surface_classifier_cache_entry_validb entry = false).
Proof.
  intros entries index entry Hlookup.
  pose proof (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
    entries index index entry entry Hlookup Hlookup) as Hinvalid.
  split.
  - intro H.
    destruct (proj1 Hinvalid H) as [Hb | Hb]; exact Hb.
  - intro Hb.
    apply (proj2 Hinvalid). left. exact Hb.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_diagonal_witness_iff :
  forall entries index,
    phase1_surface_classifier_cache_batch_compare_at entries index index =
      Some Phase1CacheInvalid <->
    exists entry, nth_error entries index = Some entry /\
      phase1_surface_classifier_cache_entry_validb entry = false.
Proof.
  intros entries index.
  split.
  - intro H.
    destruct (nth_error entries index) as [entry|] eqn:Hlookup.
    + exists entry. split; [reflexivity|].
      exact (proj1
        (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
          entries index entry Hlookup) H).
    + assert (Hmissing :
        phase1_surface_classifier_cache_batch_compare_at entries index index = None).
      { apply (proj2
          (phase1_surface_classifier_cache_batch_compare_at_missing_iff
            entries index index)). left. exact Hlookup. }
      rewrite Hmissing in H. discriminate H.
  - intros [entry [Hlookup Hb]].
    exact (proj2
      (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
        entries index entry Hlookup) Hb).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_diagonals_valid_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_validb entries = true <->
    forall index,
      phase1_surface_classifier_cache_batch_compare_at entries index index <>
        Some Phase1CacheInvalid.
Proof.
  intro entries. split.
  - intros Hv index H.
    destruct (proj1
      (phase1_surface_classifier_cache_batch_compare_diagonal_witness_iff
        entries index) H) as [entry [Hlookup Hb]].
    apply nth_error_In in Hlookup.
    pose proof (phase1_surface_classifier_cache_batch_member_valid
      entries entry Hv Hlookup) as He.
    rewrite He in Hb. discriminate Hb.
  - intro H.
    destruct (phase1_surface_classifier_cache_batch_indexed_invalid entries)
      as [[index bad]|] eqn:Hdiagnostic.
    + destruct (proj1
        (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff
          entries index bad) Hdiagnostic) as [Hlookup [_ Hb]].
      exfalso. apply (H index).
      exact (proj2
        (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
          entries index bad Hlookup) Hb).
    + exact (proj1
        (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff
          entries) Hdiagnostic).
Qed.

Theorem phase1_surface_classifier_cache_batch_first_invalid_diagonal_iff :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries =
      Some (index, bad) <->
    nth_error entries index = Some bad /\
    phase1_surface_classifier_cache_batch_validb (firstn index entries) = true /\
    phase1_surface_classifier_cache_batch_compare_at entries index index =
      Some Phase1CacheInvalid.
Proof.
  intros entries index bad. split.
  - intro H.
    destruct (proj1
      (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff
        entries index bad) H) as [Hlookup [Hp Hb]].
    split; [exact Hlookup|].
    split; [exact Hp|].
    exact (proj2
      (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
        entries index bad Hlookup) Hb).
  - intros [Hlookup [Hp Hcompare]].
    apply (proj2
      (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff
        entries index bad)).
    split; [exact Hlookup|].
    split; [exact Hp|].
    exact (proj1
      (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
        entries index bad Hlookup) Hcompare).
Qed.

Example phase1_surface_classifier_cache_batch_compare_diagonal_boundary :
  forall good bad,
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) O O <> Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S O) (S O) = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S (S O)) (S (S O)) = None.
Proof.
  intros good bad Hg Hb. split.
  - intro H.
    pose proof (proj1
      (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
        (good :: bad :: nil) O good eq_refl) H) as Hbad.
    rewrite Hg in Hbad. discriminate Hbad.
  - split.
    + exact (proj2
        (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
          (good :: bad :: nil) (S O) bad eq_refl) Hb).
    + reflexivity.
Qed.
