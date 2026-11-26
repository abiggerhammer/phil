From Stdlib Require Import Lists.List Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticReplacement.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: declaration-preserving refresh.
   Recompute the classifier for precisely the diagnosed occurrence.
   Ordered declaration projection is unchanged, and remaining invalid
   occurrences retain their original indices. No persistent freshness,
   performance, admission authority, production binding, grammar, TCB,
   G2/G4 or Phase 1 closure claim. *)

Definition phase1_surface_classifier_cache_entry_refresh
  (entry : Phase1SurfaceClassifierCacheEntry) : Phase1SurfaceClassifierCacheEntry :=
  (fst entry, phase1_surface_normalized_observation (fst entry)).

Theorem phase1_surface_classifier_cache_entry_refresh_valid :
  forall entry,
    phase1_surface_classifier_cache_entry_validb (phase1_surface_classifier_cache_entry_refresh entry) = true.
Proof.
  intro entry.
  change (phase1_surface_classifier_cache_validb (fst entry)
    (phase1_surface_normalized_observation (fst entry)) = true).
  apply (proj2 (phase1_surface_classifier_cache_validb_iff
    (fst entry) (phase1_surface_normalized_observation (fst entry)))).
  reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_refresh :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ phase1_surface_classifier_cache_entry_refresh bad :: skipn (S index) entries) =
    option_map (fun p => (S index + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries)).
Proof.
  intros entries index bad H.
  exact (phase1_surface_classifier_cache_batch_indexed_invalid_replace_valid
    entries index bad (phase1_surface_classifier_cache_entry_refresh bad) H (phase1_surface_classifier_cache_entry_refresh_valid bad)).
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_refresh_declarations :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    map fst (firstn index entries ++ phase1_surface_classifier_cache_entry_refresh bad ::
      skipn (S index) entries) = map fst entries.
Proof.
  intros entries index bad H.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  repeat rewrite map_app.
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_refresh_valid_suffix :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_validb (skipn (S index) entries) = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ phase1_surface_classifier_cache_entry_refresh bad :: skipn (S index) entries) = None.
Proof.
  intros entries index bad H Hs.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_refresh entries index bad H).
  rewrite (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff (skipn (S index) entries)) Hs).
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_refresh_duplicate :
  forall entries index bad suffix,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    skipn (S index) entries = bad :: suffix ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ phase1_surface_classifier_cache_entry_refresh bad :: skipn (S index) entries) = Some (S index, bad).
Proof.
  intros entries index bad suffix H Hs.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H) as [_ [_ Hb]].
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_refresh entries index bad H).
  rewrite Hs.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_head bad suffix Hb).
  change (Some (S index + O, bad) = Some (S index, bad)).
  now rewrite Nat.add_0_r.
Qed.
