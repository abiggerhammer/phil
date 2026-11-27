From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticRefresh
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchRefreshAll.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: canonical representatives of
   ordered declaration projections. Refresh factors through declarations;
   each projection has exactly one valid cache batch. No persistent
   freshness, performance, admission authority, production binding,
   grammar, TCB, G2/G4 or Phase 1 closure claim. *)

Definition phase1_surface_classifier_cache_batch_from_declarations
  (declarations : list Phase1SurfaceDeclarationSpine)
  : list Phase1SurfaceClassifierCacheEntry :=
  map (fun declaration =>
    (declaration, phase1_surface_normalized_observation declaration))
    declarations.

Theorem phase1_surface_classifier_cache_batch_refresh_all_factorization :
  forall entries,
    phase1_surface_classifier_cache_batch_refresh_all entries =
    phase1_surface_classifier_cache_batch_from_declarations (map fst entries).
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - reflexivity.
  - change (phase1_surface_classifier_cache_entry_refresh entry ::
      phase1_surface_classifier_cache_batch_refresh_all rest =
      phase1_surface_classifier_cache_entry_refresh entry ::
      phase1_surface_classifier_cache_batch_from_declarations (map fst rest)).
    now rewrite IH.
Qed.

Theorem phase1_surface_classifier_cache_batch_from_declarations_projection :
  forall declarations,
    map fst (phase1_surface_classifier_cache_batch_from_declarations declarations) =
    declarations.
Proof.
  intro declarations.
  induction declarations as [|declaration rest IH].
  - reflexivity.
  - change (declaration ::
      map fst (phase1_surface_classifier_cache_batch_from_declarations rest) =
      declaration :: rest).
    now rewrite IH.
Qed.

Theorem phase1_surface_classifier_cache_batch_from_declarations_valid :
  forall declarations,
    phase1_surface_classifier_cache_batch_validb
      (phase1_surface_classifier_cache_batch_from_declarations declarations) = true.
Proof.
  intro declarations.
  induction declarations as [|declaration rest IH].
  - reflexivity.
  - change ((phase1_surface_classifier_cache_entry_validb
      (phase1_surface_classifier_cache_entry_refresh (declaration, None)) &&
      phase1_surface_classifier_cache_batch_validb
        (phase1_surface_classifier_cache_batch_from_declarations rest)) = true).
    now rewrite phase1_surface_classifier_cache_entry_refresh_valid, IH.
Qed.

Theorem phase1_surface_classifier_cache_batch_refresh_all_eq_iff :
  forall left right,
    phase1_surface_classifier_cache_batch_refresh_all left =
    phase1_surface_classifier_cache_batch_refresh_all right <->
    map fst left = map fst right.
Proof.
  intros left right. split.
  - intro H.
    pose proof (f_equal (map fst) H) as Hp.
    now rewrite !phase1_surface_classifier_cache_batch_refresh_all_declarations in Hp.
  - intro H.
    rewrite !phase1_surface_classifier_cache_batch_refresh_all_factorization.
    now rewrite H.
Qed.

Theorem phase1_surface_classifier_cache_batch_valid_projection_unique :
  forall entries other,
    phase1_surface_classifier_cache_batch_validb other = true ->
    map fst other = map fst entries ->
    other = phase1_surface_classifier_cache_batch_refresh_all entries.
Proof.
  intros entries other Hv Hp.
  transitivity (phase1_surface_classifier_cache_batch_refresh_all other).
  - symmetry.
    exact (proj2 (phase1_surface_classifier_cache_batch_refresh_all_fixed_iff other) Hv).
  - exact (proj2 (phase1_surface_classifier_cache_batch_refresh_all_eq_iff other entries) Hp).
Qed.

Example phase1_surface_classifier_cache_batch_canonical_duplicate_distinct :
  forall declaration,
    phase1_surface_classifier_cache_batch_from_declarations
      (declaration :: declaration :: nil) <>
    phase1_surface_classifier_cache_batch_from_declarations (declaration :: nil).
Proof.
  intros declaration H.
  pose proof (f_equal (map fst) H) as Hp.
  rewrite !phase1_surface_classifier_cache_batch_from_declarations_projection in Hp.
  discriminate Hp.
Qed.
