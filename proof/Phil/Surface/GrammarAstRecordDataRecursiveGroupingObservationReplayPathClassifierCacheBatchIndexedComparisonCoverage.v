From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathGuardedCacheComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchValidation
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnostic
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedDiagnosticLookup
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparison
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierCacheBatchIndexedComparisonDiagnostics.

(* PHIL-SURFACE-GRAMMAR-CORR-001 G3: positional comparison coverage.
   At present positions, invalid pair comparison factors through its
   diagonals; successful comparison identifies exact canonical evidence
   and replay result. The first invalid occurrence poisons its row only
   at present columns. Whole-batch validity is equivalent to exact
   replay comparison at every present pair. No persistent freshness,
   performance, admission authority, production binding, grammar, TCB,
   G2/G4 or Phase 1 closure claim. *)

Theorem phase1_surface_classifier_cache_batch_compare_at_diagonals_iff :
  forall entries i j left right,
    nth_error entries i = Some left ->
    nth_error entries j = Some right ->
    (phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some Phase1CacheInvalid <->
     phase1_surface_classifier_cache_batch_compare_at entries i i =
       Some Phase1CacheInvalid \/
     phase1_surface_classifier_cache_batch_compare_at entries j j =
       Some Phase1CacheInvalid).
Proof.
  intros entries i j left right Hl Hr.
  pose proof (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
    entries i j left right Hl Hr) as Hp.
  pose proof (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
    entries i left Hl) as Hi.
  pose proof (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
    entries j right Hr) as Hj.
  split.
  - intro H. destruct (proj1 Hp H) as [Hbad|Hbad].
    + left. exact (proj2 Hi Hbad).
    + right. exact (proj2 Hj Hbad).
  - intros [Hbad|Hbad]; apply (proj2 Hp).
    + left. exact (proj1 Hi Hbad).
    + right. exact (proj1 Hj Hbad).
Qed.

Theorem phase1_surface_classifier_cache_batch_compare_at_compared_exact_iff :
  forall entries i j left right comparison,
    nth_error entries i = Some left ->
    nth_error entries j = Some right ->
    (phase1_surface_classifier_cache_batch_compare_at entries i j =
      Some (Phase1CacheCompared comparison) <->
     snd left = phase1_surface_normalized_observation (fst left) /\
     snd right = phase1_surface_normalized_observation (fst right) /\
     comparison = phase1_surface_replay_compare (fst left) (fst right)).
Proof.
  intros entries i j left right comparison Hl Hr.
  unfold phase1_surface_classifier_cache_batch_compare_at.
  rewrite Hl, Hr.
  pose proof (phase1_surface_guarded_cache_compare_compared_iff
    (fst left) (fst right) (snd left) (snd right) comparison) as Hexact.
  split.
  - intro H. injection H as Hcompare.
    exact (proj1 Hexact Hcompare).
  - intro H.
    exact (f_equal (@Some Phase1SurfaceGuardedCacheComparison)
      (proj2 Hexact H)).
Qed.

Theorem phase1_surface_classifier_cache_batch_first_invalid_row_iff :
  forall entries index bad j,
    phase1_surface_classifier_cache_batch_indexed_invalid entries =
      Some (index, bad) ->
    (phase1_surface_classifier_cache_batch_compare_at entries index j =
       Some Phase1CacheInvalid <-> nth_error entries j <> None).
Proof.
  intros entries index bad j Hdiagnostic.
  destruct (proj1
    (phase1_surface_classifier_cache_batch_indexed_invalid_lookup_iff
      entries index bad) Hdiagnostic) as [Hl [_ Hb]].
  destruct (nth_error entries j) as [right|] eqn:Hr.
  - split.
    + intros _ Hnone. discriminate Hnone.
    + intros _.
      apply (proj2
        (phase1_surface_classifier_cache_batch_compare_at_invalid_iff
          entries index j bad right Hl Hr)).
      left. exact Hb.
  - assert (Hmissing :
      phase1_surface_classifier_cache_batch_compare_at entries index j = None).
    { apply (proj2
        (phase1_surface_classifier_cache_batch_compare_at_missing_iff
          entries index j)). right. exact Hr. }
    split.
    + intro H. rewrite Hmissing in H. discriminate H.
    + intro H. exfalso. apply H. reflexivity.
Qed.

Theorem phase1_surface_classifier_cache_batch_all_present_pairs_replay_iff :
  forall entries,
    phase1_surface_classifier_cache_batch_validb entries = true <->
    forall i j left right,
      nth_error entries i = Some left ->
      nth_error entries j = Some right ->
      phase1_surface_classifier_cache_batch_compare_at entries i j =
        Some (Phase1CacheCompared
          (phase1_surface_replay_compare (fst left) (fst right))).
Proof.
  intro entries. split.
  - intros Hv i j left right Hl Hr.
    exact (phase1_surface_classifier_cache_batch_compare_at_valid
      entries i j left right Hv Hl Hr).
  - intro H.
    apply (proj2
      (phase1_surface_classifier_cache_batch_compare_diagonals_valid_iff
        entries)).
    intros index Hinvalid.
    destruct (proj1
      (phase1_surface_classifier_cache_batch_compare_diagonal_witness_iff
        entries index) Hinvalid) as [entry [Hlookup _]].
    pose proof (H index index entry entry Hlookup Hlookup) as Hcompared.
    rewrite Hcompared in Hinvalid. discriminate Hinvalid.
Qed.

Example phase1_surface_classifier_cache_batch_invalid_row_missing_boundary :
  forall bad,
    phase1_surface_classifier_cache_entry_validb bad = false ->
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: nil) O O = Some Phase1CacheInvalid /\
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: nil) O (S O) = None /\
    phase1_surface_classifier_cache_batch_compare_at
      (bad :: nil) (S O) O = None.
Proof.
  intros bad Hb. split.
  - exact (proj2
      (phase1_surface_classifier_cache_batch_compare_diagonal_invalid_iff
        (bad :: nil) O bad eq_refl) Hb).
  - split; reflexivity.
Qed.
