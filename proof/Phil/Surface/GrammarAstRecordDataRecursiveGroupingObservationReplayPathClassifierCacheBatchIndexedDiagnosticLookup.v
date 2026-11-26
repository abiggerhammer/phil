From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: indexed diagnostic lookup.
   Connect the exact first-invalid occurrence to ordinary list lookup and
   the valid prefix selected by firstn, without quotienting duplicates.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_prefix_lookup :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry)
    (bad : Phase1SurfaceClassifierCacheEntry) (suffix : list Phase1SurfaceClassifierCacheEntry),
    nth_error (prefix ++ bad :: suffix) (length prefix) = Some bad /\
    firstn (length prefix) (prefix ++ bad :: suffix) = prefix.
Proof.
  intro prefix.
  induction prefix as [|entry prefix IH]; intros bad suffix.
  - split; reflexivity.
  - destruct (IH bad suffix) as [Hlookup Hprefix].
    split.
    + exact Hlookup.
    + change (entry :: firstn (length prefix) (prefix ++ bad :: suffix) =
        entry :: prefix).
      now rewrite Hprefix.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) <->
    nth_error entries index = Some bad /\
    phase1_surface_classifier_cache_batch_validb (firstn index entries) = true /\
    phase1_surface_classifier_cache_entry_validb bad = false.
Proof.
  intros entries index bad.
  split.
  - intro H.
    destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
      as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
    subst entries. subst index.
    destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
      as [Hlookup Hprefix].
    split; [exact Hlookup|].
    split; [now rewrite Hprefix|exact Hb].
  - intros [Hlookup [Hp Hb]].
    apply nth_error_split in Hlookup.
    destruct Hlookup as [prefix [suffix [Heq Hi]]].
    subst entries. subst index.
    destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
      as [_ Hprefix].
    rewrite Hprefix in Hp.
    exact (phase1_surface_classifier_cache_batch_indexed_invalid_complete prefix bad suffix Hp Hb).
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_in_bounds :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    index < length entries.
Proof.
  intros entries index bad H.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [Hlookup _].
  apply nth_error_Some.
  rewrite Hlookup. discriminate.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_prefix_absent :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid (firstn index entries) = None.
Proof.
  intros entries index bad H.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [_ [Hp _]].
  exact (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff (firstn index entries)) Hp).
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_missing_lookup :
  forall entries index bad,
    nth_error entries index = None ->
    phase1_surface_classifier_cache_batch_indexed_invalid entries <> Some (index, bad).
Proof.
  intros entries index bad Hnone H.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [Hlookup _].
  rewrite Hnone in Hlookup. discriminate Hlookup.
Qed.
