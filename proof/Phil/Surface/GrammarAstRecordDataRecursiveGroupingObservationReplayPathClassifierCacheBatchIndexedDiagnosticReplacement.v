From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional replacement.
   Split at the first invalid occurrence and characterize the diagnostic
   after replacing only that occurrence by a validated entry.
   Replacement validity is an explicit premise; declaration identity,
   persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 and Phase 1 closure are not claimed. *)

Theorem phase1_surface_classifier_cache_batch_suffix_lookup :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry)
    (bad : Phase1SurfaceClassifierCacheEntry) (suffix : list Phase1SurfaceClassifierCacheEntry),
    skipn (S (length prefix)) (prefix ++ bad :: suffix) = suffix.
Proof.
  intro prefix.
  induction prefix as [|entry prefix IH]; intros bad suffix.
  - reflexivity.
  - change (skipn (S (length prefix)) (prefix ++ bad :: suffix) = suffix).
    exact (IH bad suffix).
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_split :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    entries = firstn index entries ++ bad :: skipn (S index) entries.
Proof.
  intros entries index bad H.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_replace_valid :
  forall entries index bad good,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ good :: skipn (S index) entries) =
    option_map (fun p => (S index + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries)).
Proof.
  intros entries index bad good H Hg.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_append_valid_left
    prefix (good :: suffix) Hp).
  change (option_map (fun p => (length prefix + fst p, snd p))
      (if phase1_surface_classifier_cache_entry_validb good
       then option_map (fun p => (S (fst p), snd p))
         (phase1_surface_classifier_cache_batch_indexed_invalid suffix)
       else Some (O, good)) =
    option_map (fun p => (S (length prefix) + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid suffix)).
  rewrite Hg.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid suffix)
    as [[i next]|].
  - change (Some (length prefix + S i, next) = Some (S (length prefix + i), next)).
    rewrite Nat.add_succ_r. reflexivity.
  - reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_replace_valid_suffix :
  forall entries index bad good,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_batch_validb (skipn (S index) entries) = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ good :: skipn (S index) entries) = None.
Proof.
  intros entries index bad good H Hg Hsuffix.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_replace_valid
    entries index bad good H Hg).
  rewrite (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff
    (skipn (S index) entries)) Hsuffix).
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_replace_next :
  forall entries index bad good j next,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries) = Some (j, next) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ good :: skipn (S index) entries) = Some (S index + j, next).
Proof.
  intros entries index bad good j next H Hg Hnext.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_replace_valid
    entries index bad good H Hg).
  rewrite Hnext. reflexivity.
Qed.
