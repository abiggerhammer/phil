From Stdlib Require Import Lists.List Bool.Bool.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: finite batch cache validation.
  Every occurrence must validate against its own declaration, including
  repeated declarations and cached None. Empty batches validate vacuously.
  A failed batch has a concrete invalid member; a successful batch
  supports guarded replay comparison of any two of its members.
  No persistent freshness, speedup, admission authority, production
  binding, grammar, TCB, G2/G4 or Phase 1 closure claim.
*)

Definition Phase1SurfaceClassifierCacheEntry : Type :=
  (Phase1SurfaceDeclarationSpine *
    option Phase1SurfaceRecursiveGroupingObservedRecordData)%type.

Definition phase1_surface_classifier_cache_entry_validb
  (entry : Phase1SurfaceClassifierCacheEntry) : bool :=
  phase1_surface_classifier_cache_validb (fst entry) (snd entry).

Definition phase1_surface_classifier_cache_batch_validb
  (entries : list Phase1SurfaceClassifierCacheEntry) : bool :=
  forallb phase1_surface_classifier_cache_entry_validb entries.

Theorem phase1_surface_classifier_cache_batch_validb_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_validb entries = true <->
    forall entry, In entry entries ->
      snd entry = phase1_surface_normalized_observation (fst entry).
Proof.
  intro entries.
  unfold phase1_surface_classifier_cache_batch_validb.
  rewrite forallb_forall.
  split.
  - intros H entry Hin.
    apply (proj1 (phase1_surface_classifier_cache_validb_iff
      (fst entry) (snd entry))).
    exact (H entry Hin).
  - intros H entry Hin.
    unfold phase1_surface_classifier_cache_entry_validb.
    apply (proj2 (phase1_surface_classifier_cache_validb_iff
      (fst entry) (snd entry))).
    exact (H entry Hin).
Qed.

Theorem phase1_surface_classifier_cache_batch_invalidb_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_validb entries = false <->
    exists entry, In entry entries /\
      phase1_surface_classifier_cache_entry_validb entry = false.
Proof.
  intro entries.
  induction entries as [|entry rest IH].
  - simpl. split.
    + intro H. discriminate H.
    + intros [bad [Hin _]]. contradiction.
  - change ((phase1_surface_classifier_cache_entry_validb entry &&
      phase1_surface_classifier_cache_batch_validb rest) = false <->
      exists bad, (entry = bad \/ In bad rest) /\
        phase1_surface_classifier_cache_entry_validb bad = false).
    rewrite andb_false_iff, IH.
    split.
    + intros [Hbad | [bad [Hin Hbad]]].
      * exists entry. split; [left; reflexivity|exact Hbad].
      * exists bad. split; [right; exact Hin|exact Hbad].
    + intros [bad [[Heq|Hin] Hbad]].
      * left. subst bad. exact Hbad.
      * right. exists bad. split; assumption.
Qed.

Theorem phase1_surface_classifier_cache_batch_member_valid :
  forall entries entry,
    phase1_surface_classifier_cache_batch_validb entries = true ->
    In entry entries ->
    phase1_surface_classifier_cache_entry_validb entry = true.
Proof.
  intros entries entry Hvalid Hin.
  unfold phase1_surface_classifier_cache_entry_validb.
  apply (proj2 (phase1_surface_classifier_cache_validb_iff
    (fst entry) (snd entry))).
  exact ((proj1 (phase1_surface_classifier_cache_batch_validb_iff
    entries) Hvalid) entry Hin).
Qed.

Theorem phase1_surface_classifier_cache_batch_pair_replay :
  forall entries left right,
    phase1_surface_classifier_cache_batch_validb entries = true ->
    In left entries -> In right entries ->
    phase1_surface_guarded_cache_compare (fst left) (fst right)
      (snd left) (snd right) =
    Phase1CacheCompared (phase1_surface_replay_compare (fst left) (fst right)).
Proof.
  intros entries left right Hvalid Hl Hr.
  apply phase1_surface_guarded_cache_compare_valid.
  - exact (phase1_surface_classifier_cache_batch_member_valid
      entries left Hvalid Hl).
  - exact (phase1_surface_classifier_cache_batch_member_valid
      entries right Hvalid Hr).
Qed.

Example phase1_surface_classifier_cache_batch_empty :
  phase1_surface_classifier_cache_batch_validb nil = true.
Proof. reflexivity. Qed.

Example phase1_surface_classifier_cache_batch_invalid_duplicate :
  forall declaration good bad,
    phase1_surface_classifier_cache_validb declaration good = true ->
    phase1_surface_classifier_cache_validb declaration bad = false ->
    phase1_surface_classifier_cache_batch_validb
      ((declaration, good) :: (declaration, bad) :: nil) = false.
Proof.
  intros declaration good bad Hgood Hbad.
  change ((phase1_surface_classifier_cache_validb declaration good &&
    (phase1_surface_classifier_cache_validb declaration bad && true)) = false).
  rewrite Hgood, Hbad. reflexivity.
Qed.
