From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierValueComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: fail closed when comparing two
  proposed classifier caches. Invalid cache evidence is distinct from
  every valid replay comparison, including coincident rejection.
  Validation recomputes observations; no freshness, admission authority,
  performance improvement, production binding, grammar, TCB, G2/G4
  or Phase 1 closure is claimed.
*)

Inductive Phase1SurfaceGuardedCacheComparison : Type :=
| Phase1CacheInvalid
| Phase1CacheCompared (comparison : Phase1SurfaceReplayComparison).

Definition phase1_surface_guarded_cache_compare
  (left right : Phase1SurfaceDeclarationSpine)
  (left_cached right_cached :
    option Phase1SurfaceRecursiveGroupingObservedRecordData)
  : Phase1SurfaceGuardedCacheComparison :=
  if phase1_surface_classifier_cache_validb left left_cached then
    if phase1_surface_classifier_cache_validb right right_cached then
      Phase1CacheCompared
        (phase1_surface_compare_classifier_values left_cached right_cached)
    else Phase1CacheInvalid
  else Phase1CacheInvalid.

Theorem phase1_surface_guarded_cache_compare_valid :
  forall left right left_cached right_cached,
    phase1_surface_classifier_cache_validb left left_cached = true ->
    phase1_surface_classifier_cache_validb right right_cached = true ->
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared (phase1_surface_replay_compare left right).
Proof.
  intros left right left_cached right_cached Hl Hr.
  unfold phase1_surface_guarded_cache_compare.
  rewrite Hl, Hr.
  pose proof (proj1 (phase1_surface_classifier_cache_validb_iff
    left left_cached) Hl) as El.
  pose proof (proj1 (phase1_surface_classifier_cache_validb_iff
    right right_cached) Hr) as Er.
  rewrite El, Er.
  rewrite (phase1_surface_compare_classifier_values_replay left right).
  reflexivity.
Qed.

Theorem phase1_surface_guarded_cache_compare_invalid_iff :
  forall left right left_cached right_cached,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheInvalid <->
    phase1_surface_classifier_cache_validb left left_cached = false \/
    phase1_surface_classifier_cache_validb right right_cached = false.
Proof.
  intros left right left_cached right_cached.
  unfold phase1_surface_guarded_cache_compare.
  destruct (phase1_surface_classifier_cache_validb left left_cached);
    destruct (phase1_surface_classifier_cache_validb right right_cached).
  - split.
    + intro H. discriminate H.
    + intros [H|H]; discriminate H.
  - split.
    + intro H. right. reflexivity.
    + intro H. reflexivity.
  - split.
    + intro H. left. reflexivity.
    + intro H. reflexivity.
  - split.
    + intro H. left. reflexivity.
    + intro H. reflexivity.
Qed.

Theorem phase1_surface_guarded_cache_compare_compared_iff :
  forall left right left_cached right_cached comparison,
    phase1_surface_guarded_cache_compare left right left_cached right_cached =
      Phase1CacheCompared comparison <->
    left_cached = phase1_surface_normalized_observation left /\
    right_cached = phase1_surface_normalized_observation right /\
    comparison = phase1_surface_replay_compare left right.
Proof.
  intros left right left_cached right_cached comparison.
  split.
  - intro H.
    destruct (phase1_surface_classifier_cache_validb left left_cached) eqn:Hl.
    + destruct (phase1_surface_classifier_cache_validb right right_cached) eqn:Hr.
      * split.
        -- exact (proj1 (phase1_surface_classifier_cache_validb_iff
             left left_cached) Hl).
        -- split.
           ++ exact (proj1 (phase1_surface_classifier_cache_validb_iff
                right right_cached) Hr).
           ++ pose proof (phase1_surface_guarded_cache_compare_valid
                left right left_cached right_cached Hl Hr) as Hexpected.
              congruence.
      * unfold phase1_surface_guarded_cache_compare in H.
        rewrite Hl, Hr in H. discriminate H.
    + unfold phase1_surface_guarded_cache_compare in H.
      rewrite Hl in H. discriminate H.
  - intros [Hl [Hr Hresult]].
    subst comparison.
    apply phase1_surface_guarded_cache_compare_valid.
    + exact (proj2 (phase1_surface_classifier_cache_validb_iff
        left left_cached) Hl).
    + exact (proj2 (phase1_surface_classifier_cache_validb_iff
        right right_cached) Hr).
Qed.

Theorem phase1_surface_guarded_cache_compare_both_rejected :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_normalized_observation right = None ->
    phase1_surface_guarded_cache_compare left right
      (@None Phase1SurfaceRecursiveGroupingObservedRecordData)
      (@None Phase1SurfaceRecursiveGroupingObservedRecordData) =
        Phase1CacheCompared Phase1ReplayBothRejected.
Proof.
  intros left right Hl Hr.
  pose proof (proj2 (phase1_surface_classifier_cache_validb_none_iff left)
    Hl) as Vl.
  pose proof (proj2 (phase1_surface_classifier_cache_validb_none_iff right)
    Hr) as Vr.
  unfold phase1_surface_guarded_cache_compare.
  rewrite Vl, Vr.
  reflexivity.
Qed.
