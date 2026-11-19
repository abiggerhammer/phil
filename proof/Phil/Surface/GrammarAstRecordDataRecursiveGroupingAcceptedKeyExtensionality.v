From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity.

Open Scope string_scope.

(*
  Bounded G3: accepted implementation values determine exactly the
  declaration tag and selected parse tree of their public input carrier.
  Conversely, successful normalization is extensional in that pair.
  Re-encoding a successfully admitted value remains accepted.

  Every theorem is conditional on actual successful normalization: no
  arbitrary public tag/tree record is presumed canonical or valid.
  In particular, the absent and present-empty requirements remain
  separate and malformed literals fail closed. No production parser
  binding, G2/G4, or Phase 1 completion is implied.
*)

Theorem phase1_surface_successful_record_data_admission_key_extensionality :
  forall (left right : Phase1SurfaceDeclarationSpine)
         left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    (left_refined = right_refined <->
      phase1_declaration_spine_tag left =
        phase1_declaration_spine_tag right /\
      phase1_declaration_spine_selected_tree left =
        phase1_declaration_spine_selected_tree right).
Proof.
  intros left right left_refined right_refined Hleft Hright.
  split.
  - intro Hequal.
    subst right_refined.
    pose proof
      (phase1_surface_recursive_grouping_tagged_admission_injective
        left right left_refined Hleft Hright) as Hkey.
    split.
    + exact (f_equal phase1_declaration_spine_tag Hkey).
    + exact (f_equal phase1_declaration_spine_selected_tree Hkey).
  - intros [Htag Htree].
    destruct left as [left_tag left_tree].
    destruct right as [right_tag right_tree].
    cbn in *.
    subst right_tag right_tree.
    rewrite Hleft in Hright.
    now inversion Hright.
Qed.

Theorem phase1_surface_successful_record_data_admission_reencode_stable :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
      = Some refined.
Proof.
  intros declaration refined Hnormalize.
  rewrite
    (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      declaration refined Hnormalize).
  exact Hnormalize.
Qed.

Example phase1_surface_accepted_key_absent_requirements_stable :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_absent_requirements_record)) =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record).
Proof.
  exact phase1_surface_tagged_absent_requirements_still_accepted.
Qed.

Example phase1_surface_accepted_key_present_empty_requirements_stable :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_present_empty_requirements_record)) =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).
Proof.
  exact phase1_surface_tagged_present_empty_requirements_still_accepted.
Qed.

Example phase1_surface_accepted_key_malformed_literal_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof.
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
