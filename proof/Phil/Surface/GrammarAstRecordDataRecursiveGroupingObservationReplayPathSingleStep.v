From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationReplayPairCoherence
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClosure
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathQuotient.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: compress arbitrary finite admitted
  Record/Data replay paths to one witnessed, successfully normalized
  replay edge. This is a proof of *path normal form*, not exact public
  key equality. Both endpoint admissions are indispensable, even when
  the path was built through multiple intermediate public carriers.

  The normal form preserves certificate-fiber transport and the
  deliberate non-injectivity of the observation quotient; an ill-tagged
  public Record key cannot be smuggled in as a path endpoint.
  Proof-side only. No new normalization or runtime algorithm, grammar
  or TCB changes, production AST binding, G2/G4, or Phase 1 closure.
*)

Definition phase1_surface_admitted_replay_single_step
  (left right : Phase1SurfaceDeclarationSpine) : Prop :=
  exists left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined /\
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined).

Theorem phase1_surface_replay_path_compresses_to_single_step :
  forall left right,
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_admitted_replay_single_step left right.
Proof.
  intros left right Hpath.
  destruct (phase1_surface_replay_path_related left right Hpath)
    as [left_refined [right_refined [Hleft [Hright Hobserved]]]].
  exists left_refined, right_refined.
  split; [exact Hleft |].
  split; [exact Hright |].
  apply (proj2 (phase1_surface_dual_replay_related_iff_observations
    left right left_refined right_refined Hleft Hright)).
  exact Hobserved.
Qed.

Theorem phase1_surface_replay_single_step_expands_to_path :
  forall left right,
    phase1_surface_admitted_replay_single_step left right ->
    phase1_surface_admitted_replay_path left right.
Proof.
  intros left right [left_refined [right_refined [Hleft [Hright Hrelated]]]].
  exact (phase1_surface_admitted_replay_path_link
    left right left_refined right_refined Hleft Hright Hrelated).
Qed.

Theorem phase1_surface_replay_path_iff_single_step :
  forall left right,
    phase1_surface_admitted_replay_path left right <->
    phase1_surface_admitted_replay_single_step left right.
Proof.
  intros left right.
  split.
  - apply phase1_surface_replay_path_compresses_to_single_step.
  - apply phase1_surface_replay_single_step_expands_to_path.
Qed.

Theorem phase1_surface_replay_path_composed_middle_eliminated :
  forall left middle right,
    phase1_surface_admitted_replay_path left middle ->
    phase1_surface_admitted_replay_path middle right ->
    phase1_surface_admitted_replay_single_step left right.
Proof.
  intros left middle right Hleft Hright.
  apply phase1_surface_replay_path_compresses_to_single_step.
  exact (phase1_surface_admitted_replay_path_compose
    left middle right Hleft Hright).
Qed.

Theorem phase1_surface_replay_single_step_certificate_fiber_transport :
  forall left right (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_admitted_replay_single_step left right ->
    (phase1_surface_recursive_grouping_observation_related
       left (phase1_admitted_observation_key entry) <->
     phase1_surface_recursive_grouping_observation_related
       right (phase1_admitted_observation_key entry)).
Proof.
  intros left right entry Hstep.
  apply phase1_surface_replay_path_certificate_fiber_transport.
  apply phase1_surface_replay_single_step_expands_to_path.
  exact Hstep.
Qed.

Theorem phase1_surface_replay_single_step_not_exact_key_equality :
  exists left right,
    phase1_surface_admitted_replay_single_step left right /\
    left <> right.
Proof.
  destruct phase1_surface_replay_path_not_exact_key_equality
    as [left [right [Hpath Hdistinct]]].
  exists left, right.
  split.
  - apply phase1_surface_replay_path_compresses_to_single_step.
    exact Hpath.
  - exact Hdistinct.
Qed.

Example phase1_surface_replay_single_step_rejects_malformed_record :
  forall other,
    ~ phase1_surface_admitted_replay_single_step
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
        other.
Proof.
  intros other [left_refined [right_refined [Hleft _]]].
  rewrite phase1_surface_impl_literal_under_record_tag_rejected in Hleft.
  discriminate Hleft.
Qed.
