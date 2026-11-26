From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchFirstInvalid
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: ordered finite batch composition.
   Concatenation preserves an earlier invalid occurrence; otherwise the
   right diagnostic is shifted by the exact length of the left batch.
   No persistent freshness, performance, admission authority, production
   binding, grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_none_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = None <->
    phase1_surface_classifier_cache_batch_validb entries = true.
Proof.
  intro entries.
  rewrite <- phase1_surface_classifier_cache_batch_first_invalid_none_iff.
  rewrite <- phase1_surface_classifier_cache_batch_indexed_invalid_projection.
  destruct (phase1_surface_classifier_cache_batch_indexed_invalid entries)
    as [[i bad]|]; simpl; split; congruence.
Qed.

Theorem phase1_surface_classifier_cache_batch_validb_append :
  forall left right,
    phase1_surface_classifier_cache_batch_validb (left ++ right) =
    (phase1_surface_classifier_cache_batch_validb left &&
     phase1_surface_classifier_cache_batch_validb right).
Proof.
  intros left right.
  unfold phase1_surface_classifier_cache_batch_validb.
  apply forallb_app.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_append :
  forall left right,
    phase1_surface_classifier_cache_batch_indexed_invalid (left ++ right) =
    match phase1_surface_classifier_cache_batch_indexed_invalid left with
    | Some p => Some p
    | None => option_map (fun p => (length left + fst p, snd p))
                (phase1_surface_classifier_cache_batch_indexed_invalid right)
    end.
Proof.
  intro left.
  induction left as [|entry left IH]; intro right.
  - cbn [app length phase1_surface_classifier_cache_batch_indexed_invalid].
    destruct (phase1_surface_classifier_cache_batch_indexed_invalid right)
      as [[i bad]|]; reflexivity.
  - cbn [app length phase1_surface_classifier_cache_batch_indexed_invalid].
    destruct (phase1_surface_classifier_cache_entry_validb entry).
    + rewrite IH.
      destruct (phase1_surface_classifier_cache_batch_indexed_invalid left)
        as [[i bad]|].
      * reflexivity.
      * destruct (phase1_surface_classifier_cache_batch_indexed_invalid right)
          as [[i bad]|]; reflexivity.
    + reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_append_valid_left :
  forall left right,
    phase1_surface_classifier_cache_batch_validb left = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid (left ++ right) =
    option_map (fun p => (length left + fst p, snd p))
      (phase1_surface_classifier_cache_batch_indexed_invalid right).
Proof.
  intros left right Hvalid.
  rewrite phase1_surface_classifier_cache_batch_indexed_invalid_append.
  rewrite (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff left) Hvalid).
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_append_left_priority :
  forall left right i bad,
    phase1_surface_classifier_cache_batch_indexed_invalid left = Some (i, bad) ->
    phase1_surface_classifier_cache_batch_indexed_invalid (left ++ right) = Some (i, bad).
Proof.
  intros left right i bad H.
  now rewrite phase1_surface_classifier_cache_batch_indexed_invalid_append, H.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_append_two_valid :
  forall left right,
    phase1_surface_classifier_cache_batch_validb left = true ->
    phase1_surface_classifier_cache_batch_validb right = true ->
    phase1_surface_classifier_cache_batch_indexed_invalid (left ++ right) = None.
Proof.
  intros left right Hl Hr.
  apply (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff (left ++ right))).
  now rewrite phase1_surface_classifier_cache_batch_validb_append, Hl, Hr.
Qed.
