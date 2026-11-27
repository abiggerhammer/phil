From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticAppend
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticRefresh.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: canonical finite batch refresh.
   Recompute each occurrence independently, preserving the ordered
   declaration projection, including duplicates. Validity is exactly
   the fixed-point condition. No persistent freshness, performance,
   admission authority, production binding, grammar, TCB, G2/G4 or
   Phase 1 closure claim. *)

Definition phase1_surface_classifier_cache_batch_refresh_all
  (entries : list Phase1SurfaceClassifierCacheEntry)
  : list Phase1SurfaceClassifierCacheEntry :=
  map phase1_surface_classifier_cache_entry_refresh entries.

Theorem phase1_surface_classifier_cache_batch_refresh_all_valid :
  forall entries,
    phase1_surface_classifier_cache_batch_validb
      (phase1_surface_classifier_cache_batch_refresh_all entries) = true.
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - reflexivity.
  - change ((phase1_surface_classifier_cache_entry_validb
      (phase1_surface_classifier_cache_entry_refresh entry) &&
      phase1_surface_classifier_cache_batch_validb
        (phase1_surface_classifier_cache_batch_refresh_all rest)) = true).
    now rewrite phase1_surface_classifier_cache_entry_refresh_valid, IH.
Qed.

Theorem phase1_surface_classifier_cache_batch_refresh_all_declarations :
  forall entries,
    map fst (phase1_surface_classifier_cache_batch_refresh_all entries) =
    map fst entries.
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - reflexivity.
  - change (fst entry ::
      map fst (phase1_surface_classifier_cache_batch_refresh_all rest) =
      fst entry :: map fst rest).
    now rewrite IH.
Qed.

Theorem phase1_surface_classifier_cache_batch_refresh_all_fixed_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_refresh_all entries = entries <->
    phase1_surface_classifier_cache_batch_validb entries = true.
Proof.
  intro entries. split.
  - intro H.
    rewrite <- H.
    apply phase1_surface_classifier_cache_batch_refresh_all_valid.
  - induction entries as [|[declaration cached] rest IH]; intro H.
    + reflexivity.
    + change ((phase1_surface_classifier_cache_entry_validb
        (declaration, cached) &&
        phase1_surface_classifier_cache_batch_validb rest) = true) in H.
      apply andb_true_iff in H as [He Hr].
      change (phase1_surface_classifier_cache_validb declaration cached = true) in He.
      apply (proj1 (phase1_surface_classifier_cache_validb_iff declaration cached)) in He.
      change (phase1_surface_classifier_cache_entry_refresh
        (declaration, cached) ::
        phase1_surface_classifier_cache_batch_refresh_all rest =
        (declaration, cached) :: rest).
      rewrite (IH Hr).
      unfold phase1_surface_classifier_cache_entry_refresh.
      simpl. now rewrite He.
Qed.

Theorem phase1_surface_classifier_cache_batch_refresh_all_idempotent :
  forall entries,
    phase1_surface_classifier_cache_batch_refresh_all
      (phase1_surface_classifier_cache_batch_refresh_all entries) =
    phase1_surface_classifier_cache_batch_refresh_all entries.
Proof.
  intro entries.
  apply (proj2 (phase1_surface_classifier_cache_batch_refresh_all_fixed_iff
    (phase1_surface_classifier_cache_batch_refresh_all entries))).
  apply phase1_surface_classifier_cache_batch_refresh_all_valid.
Qed.

Theorem phase1_surface_classifier_cache_batch_refresh_all_no_diagnostic :
  forall entries,
    phase1_surface_classifier_cache_batch_indexed_invalid
      (phase1_surface_classifier_cache_batch_refresh_all entries) = None.
Proof.
  intro entries.
  apply (proj2 (phase1_surface_classifier_cache_batch_indexed_invalid_none_iff
    (phase1_surface_classifier_cache_batch_refresh_all entries))).
  apply phase1_surface_classifier_cache_batch_refresh_all_valid.
Qed.

Example phase1_surface_classifier_cache_batch_refresh_all_duplicate :
  forall bad,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_indexed_invalid (bad :: bad :: nil) =
      Some (O, bad) /\
    phase1_surface_classifier_cache_batch_refresh_all (bad :: bad :: nil) =
      phase1_surface_classifier_cache_entry_refresh bad ::
      phase1_surface_classifier_cache_entry_refresh bad :: nil /\
    phase1_surface_classifier_cache_batch_indexed_invalid
      (phase1_surface_classifier_cache_batch_refresh_all (bad :: bad :: nil)) = None.
Proof.
  intros bad Hbad. split.
  - apply phase1_surface_classifier_cache_batch_indexed_invalid_head.
    exact Hbad.
  - split.
    + reflexivity.
    + apply phase1_surface_classifier_cache_batch_refresh_all_no_diagnostic.
Qed.
