From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchRefreshAll
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchCanonical.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional guarded comparison.
   Missing positions, invalid selected cache evidence and a successful
   comparison (including coincident rejection) are distinct outcomes.
   Only the selected entries are validated by the comparison. Canonical
   refresh gives the exact declaration-index comparison. No persistent
   freshness, performance, admission authority, production binding,
   grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Definition phase1_surface_classifier_cache_batch_compare_at
  (entries : list Phase1SurfaceClassifierCacheEntry) (i j : nat)
  : option Phase1SurfaceGuardedCacheComparison :=
  match nth_error entries i, nth_error entries j with
  | Some lentry, Some rentry =>
    Some (phase1_surface_guarded_cache_compare (fst lentry) (fst rentry)
      (snd lentry) (snd rentry))
  | _, _ => None
  end.

Theorem phase1_surface_classifier_cache_batch_canonical_lookup :
  forall declarations index,
    nth_error (phase1_surface_classifier_cache_batch_from_declarations
      declarations) index =
    option_map (fun declaration =>
      (declaration, phase1_surface_normalized_observation declaration))
      (nth_error declarations index).
Proof.
  intro declarations.
  induction declarations as [|declaration rest IH]; intro index.
  - destruct index; reflexivity.
  - destruct index as [|index].
    + reflexivity.
    + exact (IH index).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_missing_iff :
  forall entries i j,
    phase1_surface_classifier_cache_batch_compare_at entries i j = None <->
    nth_error entries i = None \/ nth_error entries j = None.
Proof.
  intros entries i j.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  destruct (nth_error entries i); destruct (nth_error entries j);
    simpl; intuition discriminate.
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_invalid_iff :
  forall entries i j left right,
    nth_error entries i = Some left ->
    nth_error entries j = Some right ->
    (phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some Phase1CacheInvalid <->
     phase1_surface_classifier_cache_entry_validb left = false \/
     phase1_surface_classifier_cache_entry_validb right = false).
Proof.
  intros entries i j left right Hl Hr.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  rewrite Hl, Hr.
  change (Some (phase1_surface_guarded_cache_compare
    (fst left) (fst right) (snd left) (snd right)) =
    Some Phase1CacheInvalid <->
    phase1_surface_classifier_cache_validb (fst left) (snd left) = false \/
    phase1_surface_classifier_cache_validb (fst right) (snd right) = false).
  pose proof (phase1_surface_guarded_cache_compare_invalid_iff
    (fst left) (fst right) (snd left) (snd right)) as Hinvalid.
  split.
  - intro H. injection H as Hcompare.
    exact (proj1 Hinvalid Hcompare).
  - intro H.
    exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
      (proj2 Hinvalid H)).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_valid :
  forall entries i j left right,
    phase1_surface_classifier_cache_batch_validb entries = true ->
    nth_error entries i = Some left ->
    nth_error entries j = Some right ->
    phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some (Phase1CacheCompared
        (phase1_surface_replay_compare (fst left) (fst right))).
Proof.
  intros entries i j left right Hv Hl Hr.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  rewrite Hl, Hr.
  apply nth_error_In in Hl.
  apply nth_error_In in Hr.
  now rewrite (phase1_surface_classifier_cache_batch_pair_replay
    entries left right Hv Hl Hr).
Qed.

Theorem phase1_surface_classifier_cache_batch_canonical_compare_at :
  forall declarations i j,
    phase1_surface_classifier_cache_batch_compare_at
      (phase1_surface_classifier_cache_batch_from_declarations declarations) i j =
    match nth_error declarations i, nth_error declarations j with
    | Some ldecl, Some rdecl =>
      Some (Phase1CacheCompared (phase1_surface_replay_compare ldecl rdecl))
    | _, _ => None
    end.
Proof.
  intros declarations i j.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  rewrite !phase1_surface_classifier_cache_batch_canonical_lookup.
  destruct (nth_error declarations i) as [left|];
    destruct (nth_error declarations j) as [right|]; try reflexivity.
  change (Some (phase1_surface_guarded_cache_compare left right
    (phase1_surface_normalized_observation left)
    (phase1_surface_normalized_observation right)) =
    Some (Phase1CacheCompared (phase1_surface_replay_compare left right))).
  rewrite phase1_surface_guarded_cache_compare_valid.
  - reflexivity.
  - apply (proj2 (phase1_surface_classifier_cache_validb_iff _ _)).
    reflexivity.
  - apply (proj2 (phase1_surface_classifier_cache_validb_iff _ _)).
    reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_refreshed_compare_at :
  forall entries i j,
    phase1_surface_classifier_cache_batch_compare_at
      (phase1_surface_classifier_cache_batch_refresh_all entries) i j =
    match nth_error (map fst entries) i, nth_error (map fst entries) j with
    | Some ldecl, Some rdecl =>
      Some (Phase1CacheCompared (phase1_surface_replay_compare ldecl rdecl))
    | _, _ => None
    end.
Proof.
  intros entries i j.
  rewrite phase1_surface_classifier_cache_batch_refresh_all_factorization.
  apply phase1_surface_classifier_cache_batch_canonical_compare_at.
Qed.

Example phase1_surface_classifier_cache_batch_compare_at_rejected_duplicate :
  forall declaration,
    phase1_surface_normalized_observation declaration = None ->
    phase1_surface_classifier_cache_batch_compare_at
      (phase1_surface_classifier_cache_batch_from_declarations
        (declaration :: declaration :: nil)) O (S O) =
      Some (Phase1CacheCompared Phase1ReplayBothRejected) /\
    phase1_surface_classifier_cache_batch_compare_at
      (phase1_surface_classifier_cache_batch_from_declarations
        (declaration :: declaration :: nil)) O (S (S O)) = None.
Proof.
  intros declaration Hreject.
  rewrite !phase1_surface_classifier_cache_batch_canonical_compare_at.
  split.
  - change (Some (Phase1CacheCompared
      (phase1_surface_replay_compare declaration declaration)) =
      Some (Phase1CacheCompared Phase1ReplayBothRejected)).
    assert (Hcompare : phase1_surface_replay_compare declaration declaration =
      Phase1ReplayBothRejected).
    { apply (proj2 (phase1_surface_replay_comparison_rejected_iff
        declaration declaration)). split; exact Hreject. }
    now rewrite Hcompare.
  - reflexivity.
Qed.
