From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonLaws.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional comparison under replacement.
   Replace one occurrence, without identifying distinct positions containing
   equal entries. Lookups and comparisons avoiding that position are unchanged,
   including missing positions; the edited row checks the replacement and the
   selected unchanged entry. No declaration-identity, persistent freshness,
   performance, admission authority, production binding, grammar, TCB,
   G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_replacement_lookup_at :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry) replacement suffix,
    nth_error (prefix ++ replacement :: suffix) (length prefix) =
    Some replacement.
Proof.
  intro prefix.
  induction prefix as [|entry rest IH]; intros replacement suffix.
  - reflexivity.
  - exact (IH replacement suffix).
Qed.

Theorem phase1_surface_classifier_cache_batch_replacement_lookup_off :
  forall (prefix : list Phase1SurfaceClassifierCacheEntry) old replacement suffix i,
    i <> length prefix ->
    nth_error (prefix ++ replacement :: suffix) i =
    nth_error (prefix ++ old :: suffix) i.
Proof.
  intro prefix.
  induction prefix as [|entry rest IH]; intros old replacement suffix i Hneq;
    destruct i as [|i].
  - exfalso. apply Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
  - change (nth_error (rest ++ replacement :: suffix) i =
      nth_error (rest ++ old :: suffix) i).
    apply IH. intro Heq. apply Hneq. now rewrite Heq.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_replacement_off :
  forall prefix old replacement suffix i j,
    i <> length prefix ->
    j <> length prefix ->
    phase1_surface_classifier_cache_batch_compare_at
      (prefix ++ replacement :: suffix) i j =
    phase1_surface_classifier_cache_batch_compare_at
      (prefix ++ old :: suffix) i j.
Proof.
  intros prefix old replacement suffix i j Hi Hj.
  apply phase1_surface_classifier_cache_batch_compare_at_lookup_congruence.
  - apply phase1_surface_classifier_cache_batch_replacement_lookup_off. exact Hi.
  - apply phase1_surface_classifier_cache_batch_replacement_lookup_off. exact Hj.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_replacement_row :
  forall prefix old replacement suffix j,
    j <> length prefix ->
    phase1_surface_classifier_cache_batch_compare_at
      (prefix ++ replacement :: suffix) (length prefix) j =
    match nth_error (prefix ++ old :: suffix) j with
    | Some rentry =>
      Some (phase1_surface_guarded_cache_compare
        (fst replacement) (fst rentry) (snd replacement) (snd rentry))
    | None => None
    end.
Proof.
  intros prefix old replacement suffix j Hj.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  rewrite phase1_surface_classifier_cache_batch_replacement_lookup_at.
  rewrite (phase1_surface_classifier_cache_batch_replacement_lookup_off prefix old replacement suffix j Hj).
  reflexivity.
Qed.

Example phase1_surface_classifier_cache_batch_compare_at_replacement_duplicate_boundary :
  forall good bad,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) O O =
    phase1_surface_classifier_cache_batch_compare_at
      (good :: good :: nil) O O /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S O) (S O) = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (good :: bad :: nil) (S O) (S (S O)) = None.
Proof.
  intros good bad Hb. split.
  - reflexivity.
  - split.
    + apply (proj2
        (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
          (good :: bad :: nil) (S O) (S O) bad bad eq_refl eq_refl)).
      left. exact Hb.
    + reflexivity.
Qed.
