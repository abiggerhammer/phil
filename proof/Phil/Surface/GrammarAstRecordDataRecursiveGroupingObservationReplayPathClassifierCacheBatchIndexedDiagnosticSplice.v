From Stdlib Require Import Lists.List Arith.PeanoNat.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticReplacement.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: ordered batch splice.
   Replace exactly the diagnosed occurrence by a finite batch, preserving
   the earlier prefix and later suffix. Invalid inserted entries take
   precedence over the suffix; a valid insertion shifts its diagnostic.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_splice :
  forall entries index bad inserted,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ (inserted ++ skipn (S index) entries)) =
    option_map (fun p => (index + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid (inserted ++ skipn (S index) entries)).
Proof.
  intros entries index bad inserted H.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid_sound entries index bad H)
    as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
  subst entries. subst index.
  destruct (phase1_surface_classifier_cache_batch_prefix_lookup prefix bad suffix)
    as [_ Hprefix].
  rewrite Hprefix.
  rewrite (phase1_surface_classifier_cache_batch_suffix_lookup prefix bad suffix).
  exact (phase1_surface_classifier_cache_batch_indexed_invalid_append_valid_left prefix (inserted ++ suffix) Hp).
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_splice_valid :
  forall entries index bad inserted,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_validb inserted = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ (inserted ++ skipn (S index) entries)) =
    option_map (fun p => (index + length inserted + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries)).
Proof.
  intros entries index bad inserted H Hv.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_splice entries index bad inserted H).
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_append_valid_left inserted (skipn (S index) entries) Hv).
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid (skipn (S index) entries))
    as [[j next]|].
  - change (Some (index + (length inserted + j), next) =
      Some (index + length inserted + j, next)).
    now rewrite Nat.add_assoc.
  - reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_splice_invalid :
  forall entries index bad inserted j next,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid inserted = Some (j, next) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ (inserted ++ skipn (S index) entries)) =
    Some (index + j, next).
Proof.
  intros entries index bad inserted j next H Hi.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_splice entries index bad inserted H).
  rewrite phase1_surface_classifier_cache_batch_indexed_invalid_append, Hi.
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_splice_two_valid :
  forall entries index bad inserted,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_validb inserted = true ->
    phase1_surface_classifier_cache_batch_validb (skipn (S index) entries) = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ (inserted ++ skipn (S index) entries)) = None.
Proof.
  intros entries index bad inserted H Hi Hs.
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_splice_valid entries index bad inserted H Hi).
  rewrite (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff (skipn (S index) entries)) Hs).
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_splice_invalid_head :
  forall entries index bad inserted,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (firstn index entries ++ ((bad :: inserted) ++ skipn (S index) entries)) =
    Some (index, bad).
Proof.
  intros entries index bad inserted H.
  destruct (proj1 (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff entries index bad) H)
    as [_ [_ Hb]].
  rewrite (phase1_surface_classifier_cache_batch_indexed_invalid_splice_invalid entries index bad (bad :: inserted) O bad H
    (phase1_surface_classifier_cache_batch_indexed_invalid_head bad inserted Hb)).
  now rewrite Nat.add_0_r.
Qed.
