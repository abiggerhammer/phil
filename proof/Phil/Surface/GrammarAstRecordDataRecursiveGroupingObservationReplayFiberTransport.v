From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationCertificateCoherence
  GrammarAstRecordDataRecursiveGroupingObservationCertificateFiberLaws
  GrammarAstRecordDataRecursiveGroupingObservationAdmissionReplay.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: certificate-indexed observation
  fibers are invariant under replay of an ACTUALLY admitted Record/Data
  key. The original and reconstructed public keys have the same fiber
  members on both sides, and replay does not admit a mismatched
  certificate, collapse Record and Data families, or admit a malformed
  tag/tree carrier.

  Every positive law assumes successful normalization. These laws do
  not identify observational equivalence with exact-key equality,
  alter Grammar-v1/TCB, bind the production Haskell AST, close G2/G4,
  or establish Phase 1 closure.
*)

Theorem phase1_surface_replay_fiber_left_transport :
  forall key refined other,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         refined) other <->
     phase1_surface_recursive_grouping_observation_related key other).
Proof.
  intros key refined other Hnormal.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    key refined Hnormal).
  tauto.
Qed.

Theorem phase1_surface_replay_fiber_right_transport :
  forall key refined other,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    (phase1_surface_recursive_grouping_observation_related other
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         refined) <->
     phase1_surface_recursive_grouping_observation_related other key).
Proof.
  intros key refined other Hnormal.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    key refined Hnormal).
  tauto.
Qed.

Theorem phase1_surface_replayed_key_belongs_to_original_fiber :
  forall key refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_recursive_grouping_observation_related key
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        refined).
Proof.
  intros key refined Hnormal.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    key refined Hnormal).
  exact (phase1_surface_recursive_grouping_observation_related_reflexive_on_admission
    key refined Hnormal).
Qed.

Theorem phase1_surface_replay_certificate_fiber_iff_observation :
  forall key refined (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         refined)
       (phase1_admitted_observation_key entry) <->
     phase1_surface_admitted_observation entry =
       phase1_surface_observe_recursive_grouping_record_data refined).
Proof.
  intros key refined entry Hnormal.
  apply (phase1_surface_certificate_fiber_membership_iff_observation
    (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
    (phase1_surface_observe_recursive_grouping_record_data refined)
    entry).
  exact (phase1_surface_observation_admitted_replay_value
    key refined Hnormal).
Qed.

Theorem phase1_surface_replay_mismatched_certificate_excluded :
  forall key refined (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_admitted_observation entry <>
      phase1_surface_observe_recursive_grouping_record_data refined ->
    ~ phase1_surface_recursive_grouping_observation_related
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          refined)
        (phase1_admitted_observation_key entry).
Proof.
  intros key refined entry Hnormal Hmismatch Hrelated.
  apply Hmismatch.
  apply (proj1 (phase1_surface_replay_certificate_fiber_iff_observation
    key refined entry Hnormal)).
  exact Hrelated.
Qed.

Theorem phase1_surface_replay_distinct_certificates_excluded :
  forall key refined
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      key = Some refined ->
    phase1_surface_admitted_observation first <>
      phase1_surface_admitted_observation second ->
    ~ (phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           refined)
         (phase1_admitted_observation_key first) /\
       phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           refined)
         (phase1_admitted_observation_key second)).
Proof.
  intros key refined first second Hnormal Hdistinct.
  exact (phase1_surface_distinct_certificates_cannot_share_successful_fiber
    (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
    (phase1_surface_observe_recursive_grouping_record_data refined)
    first second
    (phase1_surface_observation_admitted_replay_value key refined Hnormal)
    Hdistinct).
Qed.

Theorem phase1_surface_replayed_record_data_fibers_disjoint :
  forall record_tree data_tree record_refined data_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := record_tree |} =
      Some record_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := data_tree |} =
      Some data_refined ->
    ~ phase1_surface_recursive_grouping_observation_related
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          record_refined)
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          data_refined).
Proof.
  intros record_tree data_tree record_refined data_refined
    Hrecord Hdata Hrelated.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := record_tree |}
    record_refined Hrecord) in Hrelated.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree := data_tree |}
    data_refined Hdata) in Hrelated.
  apply (phase1_surface_recursive_grouping_record_data_observation_classes_disjoint
    record_tree data_tree).
  exact Hrelated.
Qed.

Example phase1_surface_rejected_record_key_has_no_replay_certificate :
  ~ exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}.
Proof.
  eapply phase1_surface_rejected_key_has_no_admitted_observation_representative.
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
