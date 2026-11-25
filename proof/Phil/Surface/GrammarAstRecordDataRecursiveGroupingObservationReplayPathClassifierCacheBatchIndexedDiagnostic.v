From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchFirstInvalid.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: zero-based occurrence diagnostics.
   Preserve the earlier diagnostic by projection; identify the exact index
   of the first invalid occurrence even in batches with repeated declarations.
   No persistent cache freshness, admission, production binding, performance,
   grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Fixpoint phase1_surface_classifier_cache_batch_indexed_invalid
  (entries : list Phase1SurfaceClassifierCacheEntry)
  : option (nat * Phase1SurfaceClassifierCacheEntry) :=
  match entries with
  | nil => None
  | entry :: rest =>
      if phase1_surface_classifier_cache_entry_validb entry
      then option_map (fun p => (S (fst p), snd p))
             (phase1_surface_classifier_cache_batch_indexed_invalid rest)
      else Some (O, entry)
  end.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_projection :
  forall entries,
    option_map snd (phase1_surface_classifier_cache_batch_indexed_invalid entries) =
    phase1_surface_classifier_cache_batch_first_invalid entries.
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - reflexivity.
  - change (option_map snd
      (if phase1_surface_classifier_cache_entry_validb entry
       then option_map (fun p => (S (fst p), snd p))
         (phase1_surface_classifier_cache_batch_indexed_invalid rest)
       else Some (O, entry)) =
      (if phase1_surface_classifier_cache_entry_validb entry
       then phase1_surface_classifier_cache_batch_first_invalid rest
       else Some entry)).
    destruct (phase1_surface_classifier_cache_entry_validb entry).
    + destruct (phase1_surface_classifier_cache_batch_indexed_invalid rest)
        as [[i bad]|]; exact IH.
    + reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_sound :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) ->
    exists prefix suffix,
      entries = prefix ++ bad :: suffix /\
      index = length prefix /\
      phase1_surface_classifier_cache_batch_validb prefix = true /\
      phase1_surface_classifier_cache_entry_validb bad = false.
Proof.
  intro entries.
  induction entries as [|entry rest IH]; intros index bad H.
  - discriminate H.
  - change ((if phase1_surface_classifier_cache_entry_validb entry
      then option_map (fun p => (S (fst p), snd p))
        (phase1_surface_classifier_cache_batch_indexed_invalid rest)
      else Some (O, entry)) = Some (index, bad)) in H.
    destruct (phase1_surface_classifier_cache_entry_validb entry) eqn:Hv.
    + destruct (phase1_surface_classifier_cache_batch_indexed_invalid rest)
        as [[i found]|] eqn:Hr.
      * cbn in H. injection H as Hindex Hbad. subst index bad.
        destruct (IH i found eq_refl) as [prefix [suffix [Heq [Hi [Hp Hb]]]]].
        exists (entry :: prefix), suffix.
        split.
        -- change (entry :: rest = entry :: (prefix ++ found :: suffix)).
           now rewrite Heq.
        -- split.
           ++ simpl. now rewrite Hi.
           ++ split.
              ** change ((phase1_surface_classifier_cache_entry_validb entry &&
                    phase1_surface_classifier_cache_batch_validb prefix) = true).
                 now rewrite Hv, Hp.
              ** exact Hb.
      * discriminate H.
    + injection H as Hindex Hbad. subst index bad.
      exists nil, rest. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|exact Hv].
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_complete :
  forall prefix bad suffix,
    phase1_surface_classifier_cache_batch_validb prefix = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_indexed_invalid
      (prefix ++ bad :: suffix) = Some (length prefix, bad).
Proof.
  intro prefix.
  induction prefix as [|entry prefix IH]; intros bad suffix Hp Hb.
  - change ((if phase1_surface_classifier_cache_entry_validb bad
      then option_map (fun p => (S (fst p), snd p))
        (phase1_surface_classifier_cache_batch_indexed_invalid suffix)
      else Some (O, bad)) = Some (O, bad)).
    now rewrite Hb.
  - change ((phase1_surface_classifier_cache_entry_validb entry &&
      phase1_surface_classifier_cache_batch_validb prefix) = true) in Hp.
    apply andb_true_iff in Hp as [He Hp].
    change ((if phase1_surface_classifier_cache_entry_validb entry
      then option_map (fun p => (S (fst p), snd p))
        (phase1_surface_classifier_cache_batch_indexed_invalid (prefix ++ bad :: suffix))
      else Some (O, entry)) = Some (S (length prefix), bad)).
    rewrite He, (IH bad suffix Hp Hb). reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_indexed_invalid_iff :
  forall entries index bad,
    phase1_surface_classifier_cache_batch_indexed_invalid entries = Some (index, bad) <->
    exists prefix suffix,
      entries = prefix ++ bad :: suffix /\
      index = length prefix /\
      phase1_surface_classifier_cache_batch_validb prefix = true /\
      phase1_surface_classifier_cache_entry_validb bad = false.
Proof.
  intros entries index bad. split.
  - apply phase1_surface_classifier_cache_batch_indexed_invalid_sound.
  - intros [prefix [suffix [Heq [Hi [Hp Hb]]]]].
    rewrite Heq, Hi.
    apply phase1_surface_classifier_cache_batch_indexed_invalid_complete; assumption.
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_head :
  forall bad suffix,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_indexed_invalid (bad :: suffix) = Some (O, bad).
Proof.
  intros bad suffix Hb.
  exact (phase1_surface_classifier_cache_batch_indexed_invalid_complete nil bad suffix eq_refl Hb).
Qed.

Example phase1_surface_classifier_cache_batch_indexed_invalid_second :
  forall good bad suffix,
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_indexed_invalid (good :: bad :: suffix) = Some (1, bad).
Proof.
  intros good bad suffix Hg Hb.
  apply (phase1_surface_classifier_cache_batch_indexed_invalid_complete (good :: nil) bad suffix).
  - change ((phase1_surface_classifier_cache_entry_validb good && true) = true).
    now rewrite Hg.
  - exact Hb.
Qed.
