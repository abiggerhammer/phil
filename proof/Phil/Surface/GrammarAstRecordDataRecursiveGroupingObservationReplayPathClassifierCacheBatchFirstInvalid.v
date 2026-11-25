From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: ordered finite cache diagnostics.
   Report the first invalid occurrence, not merely an invalid declaration.
   A returned entry has a valid preceding prefix and is itself invalid.
   None is exactly batch validity. No cache freshness, performance,
   admission authority, production binding, grammar, TCB, G2/G4 or
   Phase 1 closure claim. *)

Fixpoint phase1_surface_classifier_cache_batch_first_invalid
  (entries : list Phase1SurfaceClassifierCacheEntry)
  : option Phase1SurfaceClassifierCacheEntry :=
  match entries with
  | nil => None
  | entry :: rest =>
      if phase1_surface_classifier_cache_entry_validb entry
      then phase1_surface_classifier_cache_batch_first_invalid rest
      else Some entry
  end.

Theorem phase1_surface_classifier_cache_batch_first_invalid_none_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_first_invalid entries = None <->
    phase1_surface_classifier_cache_batch_validb entries = true.
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - simpl. split; reflexivity.
  - change ((if phase1_surface_classifier_cache_entry_validb entry
      then phase1_surface_classifier_cache_batch_first_invalid rest else Some entry) = None <->
      (phase1_surface_classifier_cache_entry_validb entry &&
        phase1_surface_classifier_cache_batch_validb rest) = true).
    destruct (phase1_surface_classifier_cache_entry_validb entry);
      simpl.
    + exact IH.
    + split; discriminate.
Qed.

Theorem phase1_surface_classifier_cache_batch_first_invalid_some_sound :
  forall entries bad,
    phase1_surface_classifier_cache_batch_first_invalid entries = Some bad ->
    exists prefix suffix,
      entries = prefix ++ bad :: suffix /\
      phase1_surface_classifier_cache_batch_validb prefix = true /\
      phase1_surface_classifier_cache_entry_validb bad = false.
Proof.
  intro entries.
  induction entries as [|entry rest IH]; intros bad H.
  - discriminate H.
  - change ((if phase1_surface_classifier_cache_entry_validb entry
      then phase1_surface_classifier_cache_batch_first_invalid rest else Some entry) = Some bad) in H.
    destruct (phase1_surface_classifier_cache_entry_validb entry) eqn:Hv.
    + destruct (IH bad H) as [prefix [suffix [Heq [Hp Hb]]]].
      exists (entry :: prefix), suffix.
      split.
      * change (entry :: rest = entry :: (prefix ++ bad :: suffix)).
        now rewrite Heq.
      * split.
        -- change ((phase1_surface_classifier_cache_entry_validb entry &&
             phase1_surface_classifier_cache_batch_validb prefix) = true).
           now rewrite Hv, Hp.
        -- exact Hb.
    + injection H as Hsame. subst bad.
      exists nil, rest. split; [reflexivity|].
      split; [reflexivity|exact Hv].
Qed.

Theorem phase1_surface_classifier_cache_batch_first_invalid_some_complete :
  forall prefix bad suffix,
    phase1_surface_classifier_cache_batch_validb prefix = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_first_invalid (prefix ++ bad :: suffix) = Some bad.
Proof.
  intro prefix.
  induction prefix as [|entry prefix IH]; intros bad suffix Hp Hb.
  - change ((if phase1_surface_classifier_cache_entry_validb bad
      then phase1_surface_classifier_cache_batch_first_invalid suffix else Some bad) = Some bad).
    now rewrite Hb.
  - change ((phase1_surface_classifier_cache_entry_validb entry &&
      phase1_surface_classifier_cache_batch_validb prefix) = true) in Hp.
    apply andb_true_iff in Hp as [He Hp].
    change ((if phase1_surface_classifier_cache_entry_validb entry
      then phase1_surface_classifier_cache_batch_first_invalid (prefix ++ bad :: suffix)
      else Some entry) = Some bad).
    rewrite He. apply IH; assumption.
Qed.

Theorem phase1_surface_classifier_cache_batch_first_invalid_some_iff :
  forall entries bad,
    phase1_surface_classifier_cache_batch_first_invalid entries = Some bad <->
    exists prefix suffix,
      entries = prefix ++ bad :: suffix /\
      phase1_surface_classifier_cache_batch_validb prefix = true /\
      phase1_surface_classifier_cache_entry_validb bad = false.
Proof.
  intros entries bad. split.
  - apply phase1_surface_classifier_cache_batch_first_invalid_some_sound.
  - intros [prefix [suffix [Heq [Hp Hb]]]].
    rewrite Heq. apply phase1_surface_classifier_cache_batch_first_invalid_some_complete; assumption.
Qed.

Example phase1_surface_classifier_cache_batch_first_invalid_bad_head :
  forall bad suffix,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_first_invalid (bad :: suffix) = Some bad.
Proof.
  intros bad suffix Hb.
  exact (phase1_surface_classifier_cache_batch_first_invalid_some_complete nil bad suffix eq_refl Hb).
Qed.

Example phase1_surface_classifier_cache_batch_first_invalid_skip_valid_head :
  forall good bad suffix,
    phase1_surface_classifier_cache_entry_validb good = true ->
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_first_invalid (good :: bad :: suffix) = Some bad.
Proof.
  intros good bad suffix Hg Hb.
  change ((if phase1_surface_classifier_cache_entry_validb good
    then (if phase1_surface_classifier_cache_entry_validb bad
          then phase1_surface_classifier_cache_batch_first_invalid suffix else Some bad)
    else Some good) = Some bad).
  now rewrite Hg, Hb.
Qed.
