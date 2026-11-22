From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationCertificateCoherence
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClosure
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathQuotient.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: give finite admitted Record/Data
  replay-path connectivity a concrete, fail-closed classifier contract.
  Connectivity is exactly equality of SOME successful normalized
  observations; equal None classifications never imply connectivity.
  Every connected pair has a real admitted certificate representative,
  and certificate-fiber membership agrees with its observed class.

  Proof-side correspondence only. No grammar/TCB or normalization
  change, exact-key injectivity, Haskell AST binding, G2/G4 result,
  or Phase 1 closure.
*)

Theorem phase1_surface_replay_path_iff_same_successful_classifier :
  forall left right,
    phase1_surface_admitted_replay_path left right <->
    exists observed,
      phase1_surface_normalized_observation left = Some observed /\
      phase1_surface_normalized_observation right = Some observed.
Proof.
  intros left right.
  split.
  - intro Hpath.
    apply (proj1
      (phase1_surface_normalized_observation_related_iff_same_success left right)).
    apply phase1_surface_replay_path_related.
    exact Hpath.
  - intro Hsame.
    apply (proj2 (phase1_surface_replay_path_iff_related left right)).
    apply (proj2
      (phase1_surface_normalized_observation_related_iff_same_success left right)).
    exact Hsame.
Qed.

Theorem phase1_surface_replay_path_classifiers_equal_and_present :
  forall left right,
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_normalized_observation left =
      phase1_surface_normalized_observation right /\
    exists observed, phase1_surface_normalized_observation left = Some observed.
Proof.
  intros left right Hpath.
  destruct (proj1 (phase1_surface_replay_path_iff_same_successful_classifier
    left right) Hpath) as [observed [Hleft Hright]].
  split.
  - now rewrite Hleft, Hright.
  - exists observed. exact Hleft.
Qed.

Theorem phase1_surface_replay_path_equal_successful_classifiers_connect :
  forall left right observed,
    phase1_surface_normalized_observation left = Some observed ->
    phase1_surface_normalized_observation right = Some observed ->
    phase1_surface_admitted_replay_path left right.
Proof.
  intros left right observed Hleft Hright.
  apply (proj2 (phase1_surface_replay_path_iff_same_successful_classifier
    left right)).
  exists observed.
  split; assumption.
Qed.

Theorem phase1_surface_replay_path_equal_absent_classifiers_do_not_connect :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_normalized_observation right = None ->
    phase1_surface_normalized_observation left =
      phase1_surface_normalized_observation right /\
    ~ phase1_surface_admitted_replay_path left right.
Proof.
  intros left right Hleft Hright.
  split.
  - now rewrite Hleft, Hright.
  - intro Hpath.
    destruct (proj1 (phase1_surface_replay_path_iff_same_successful_classifier
      left right) Hpath) as [observed [Hsome _]].
    rewrite Hleft in Hsome.
    discriminate Hsome.
Qed.

Theorem phase1_surface_replay_path_iff_admitted_class_representative :
  forall left right,
    phase1_surface_admitted_replay_path left right <->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_surface_normalized_observation left =
        Some (phase1_surface_admitted_observation entry) /\
      phase1_surface_normalized_observation right =
        Some (phase1_surface_admitted_observation entry).
Proof.
  intros left right.
  split.
  - intro Hpath.
    destruct (phase1_surface_replay_path_related left right Hpath)
      as [left_refined [right_refined [Hleft [Hright Hobserved]]]].
    exists
      {| phase1_admitted_observation_key := left;
         phase1_admitted_observation_refined := left_refined;
         phase1_admitted_observation_certificate := Hleft |}.
    change (phase1_surface_normalized_observation left =
      Some (phase1_surface_observe_recursive_grouping_record_data left_refined) /\
      phase1_surface_normalized_observation right =
      Some (phase1_surface_observe_recursive_grouping_record_data left_refined)).
    split.
    + unfold phase1_surface_normalized_observation.
      now rewrite Hleft.
    + unfold phase1_surface_normalized_observation.
      rewrite Hright.
      now rewrite <- Hobserved.
  - intros [entry [Hleft Hright]].
    apply (proj2 (phase1_surface_replay_path_iff_same_successful_classifier
      left right)).
    exists (phase1_surface_admitted_observation entry).
    split; assumption.
Qed.

Theorem phase1_surface_replay_path_certificate_member_iff_class_label :
  forall left right observed (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_normalized_observation left = Some observed ->
    (phase1_surface_recursive_grouping_observation_related
       right (phase1_admitted_observation_key entry) <->
     phase1_surface_admitted_observation entry = observed).
Proof.
  intros left right observed entry Hpath Hleft.
  destruct (proj1 (phase1_surface_replay_path_iff_same_successful_classifier
    left right) Hpath) as [shared [Hleft_shared Hright_shared]].
  rewrite Hleft in Hleft_shared.
  injection Hleft_shared as Hsame.
  subst shared.
  apply (phase1_surface_certificate_fiber_membership_iff_observation
    right observed entry Hright_shared).
Qed.

Theorem phase1_surface_replay_path_distinct_class_labels_excluded :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    left_observed <> right_observed ->
    ~ phase1_surface_admitted_replay_path left right.
Proof.
  intros left right left_observed right_observed
    Hleft Hright Hdistinct Hpath.
  destruct (proj1 (phase1_surface_replay_path_iff_same_successful_classifier
    left right) Hpath) as [shared [Hleft_shared Hright_shared]].
  rewrite Hleft in Hleft_shared.
  rewrite Hright in Hright_shared.
  injection Hleft_shared as Heqleft.
  injection Hright_shared as Heqright.
  apply Hdistinct.
  transitivity shared.
  - exact Heqleft.
  - symmetry. exact Heqright.
Qed.

Example phase1_surface_replay_path_classifier_rejects_malformed_record :
  phase1_surface_normalized_observation
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof.
  apply (proj2 (phase1_surface_normalized_observation_none_iff_rejection _)).
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
