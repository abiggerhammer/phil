From Stdlib Require Import Lists.List Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticReplacement.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional deletion.
   Remove only the diagnosed occurrence, preserving the valid prefix and
   remaining suffix in order, including duplicate invalid entries.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_delete :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ skipn (S index) entries) =
    option_map (fun p => (index + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries)).
Proof.
  intros entries index bad H.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  exact (phase1_surface_classifier_cache_batch_indexed_invalid_append_valid_left prefix suffix Hp).
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_delete_length :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    S (length (firstn index entries ++ skipn (S index) entries)) = length entries.
Proof.
  intros entries index bad H.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  repeat rewrite length_app.
  change (S (length prefix + length suffix) = length prefix + S (length suffix)).
  symmetry. apply Nat.add_succ_r.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_delete_validb :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_validb
      (firstn index entries ++ skipn (S index) entries) =
    phase1_surface_classifier_cache_batch_validb (skipn (S index) entries).
Proof.
  intros entries index bad H.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [_ [Hp _]].
  rewrite phase1_surface_classifier_cache_batch_validb_append, Hp.
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_delete_valid_suffix :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_validb (skipn (S index) entries) = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ skipn (S index) entries) = None.
Proof.
  intros entries index bad H Hsuffix.
  apply (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff
    (firstn index entries ++ skipn (S index) entries))).
  now rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_delete_validb
    entries index bad H).
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_delete_duplicate :
  forall entries index bad suffix,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    skipn (S index) entries = bad :: suffix ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ skipn (S index) entries) = Some (index, bad).
Proof.
  intros entries index bad suffix H Hsuffix.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [_ [_ Hb]].
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_delete entries index bad H).
  rewrite Hsuffix.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_head bad suffix Hb).
  change (Some (index + O, bad) = Some (index, bad)).
  now rewrite Nat.add_0_r.
Qed.
