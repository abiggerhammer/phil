From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity
  GrammarAstRecordDataRecursiveGroupingAcceptedKeyExtensionality.

Open Scope string_scope.

(*
  Bounded G3: characterize the exact image and fibers of the public
  Record/Data implementation admission normalizer. An implementation
  value is reached by some public carrier exactly when its own tagged
  re-encoding is admitted; in that case every successful predecessor is
  the same tagged re-encoding. The result is conditional on actual
  normalization, not an assertion that arbitrary implementation values
  or publicly constructible tag/tree carriers are well formed.

  Absent versus present-empty requirements remain distinct; malformed
  literal carriers remain rejected. No Grammar-v1 modification, new
  trust, production parser binding, G2/G4, or Phase 1 closure claim.
*)

Theorem phase1_surface_record_data_implementation_admission_exact_fiber :
  forall refined declaration,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined <->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
        = Some refined /\
    declaration =
      phase1_surface_recursive_grouping_implementation_declaration_spine refined.
Proof.
  intros refined declaration.
  split.
  - intro Hnormalize.
    split.
    + exact
        (phase1_surface_successful_record_data_admission_reencode_stable
          declaration refined Hnormalize).
    + symmetry.
      exact
        (phase1_surface_recursive_grouping_implementation_tagged_round_trip
          declaration refined Hnormalize).
  - intros [Hfixed Hkey].
    subst declaration.
    exact Hfixed.
Qed.

Theorem phase1_surface_record_data_implementation_admission_image_iff :
  forall refined,
    (exists declaration,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        declaration = Some refined) <->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
        = Some refined.
Proof.
  intro refined.
  split.
  - intros [declaration Hnormalize].
    exact
      (phase1_surface_successful_record_data_admission_reencode_stable
        declaration refined Hnormalize).
  - intro Hfixed.
    exists (phase1_surface_recursive_grouping_implementation_declaration_spine
      refined).
    exact Hfixed.
Qed.

Example phase1_surface_admission_image_absent_requirements_unique_key :
  forall declaration,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration =
      Some (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_absent_requirements_record) ->
    declaration = phase1_surface_tagged_absent_requirements_spine.
Proof.
  intros declaration Hnormalize.
  unfold phase1_surface_tagged_absent_requirements_spine.
  symmetry.
  exact
    (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      declaration
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_absent_requirements_record) Hnormalize).
Qed.

Example phase1_surface_admission_image_present_empty_requirements_unique_key :
  forall declaration,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration =
      Some (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_present_empty_requirements_record) ->
    declaration = phase1_surface_tagged_present_empty_requirements_spine.
Proof.
  intros declaration Hnormalize.
  unfold phase1_surface_tagged_present_empty_requirements_spine.
  symmetry.
  exact
    (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      declaration
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_present_empty_requirements_record) Hnormalize).
Qed.

Example phase1_surface_admission_image_malformed_literal_has_no_fiber :
  forall refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      <> Some refined.
Proof.
  intros refined Hnormalize.
  rewrite phase1_surface_impl_literal_under_record_tag_rejected in Hnormalize.
  discriminate Hnormalize.
Qed.
