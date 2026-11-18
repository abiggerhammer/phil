From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission.

(*
  Bounded G3: successful tagged record/data admission is injective across
  publicly constructible declaration carriers.  No distinct selected trees
  or declaration tags may collapse to one successfully normalized value.
  This follows from the established tagged round-trip, without asserting
  that arbitrary intermediate carriers are well formed.  The distinct
  absent and present-empty requirements representations stay separate.
  No production parser binding or G2/G4 correspondence is claimed.
*)

Theorem phase1_surface_recursive_grouping_tagged_admission_injective :
  forall left right refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some refined ->
    left = right.
Proof.
  intros left right refined Hleft Hright.
  transitivity
    (phase1_surface_recursive_grouping_implementation_declaration_spine refined).
  - symmetry.
    exact (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      left refined Hleft).
  - exact (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      right refined Hright).
Qed.

Theorem phase1_surface_recursive_grouping_tagged_record_data_disjoint :
  forall record data_value,
    phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration record) <>
    phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationDataDeclaration data_value).
Proof.
  intros record data_value Hequal.
  apply (f_equal phase1_declaration_spine_tag) in Hequal.
  cbn in Hequal.
  discriminate Hequal.
Qed.

Definition phase1_surface_tagged_absent_requirements_spine
  : Phase1SurfaceDeclarationSpine :=
  phase1_surface_recursive_grouping_implementation_declaration_spine
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record).

Definition phase1_surface_tagged_present_empty_requirements_spine
  : Phase1SurfaceDeclarationSpine :=
  phase1_surface_recursive_grouping_implementation_declaration_spine
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).

Example phase1_surface_tagged_absent_requirements_still_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    phase1_surface_tagged_absent_requirements_spine =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_absent_requirements_record).
Proof.
  exact phase1_surface_tagged_absent_requirements_record_accepted.
Qed.

Example phase1_surface_tagged_present_empty_requirements_still_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    phase1_surface_tagged_present_empty_requirements_spine =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_present_empty_requirements_record).
Proof.
  exact phase1_surface_tagged_present_empty_requirements_record_accepted.
Qed.

Theorem phase1_surface_tagged_requirements_presence_separated :
  phase1_surface_tagged_absent_requirements_spine <>
  phase1_surface_tagged_present_empty_requirements_spine.
Proof.
  intro Hequal.
  unfold phase1_surface_tagged_absent_requirements_spine,
    phase1_surface_tagged_present_empty_requirements_spine in Hequal.
  apply (f_equal phase1_declaration_spine_selected_tree) in Hequal.
  cbn in Hequal.
  exact (phase1_surface_impl_absent_and_present_empty_are_distinct Hequal).
Qed.

Theorem phase1_surface_tagged_requirements_presence_not_collapsed :
  ~ exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        phase1_surface_tagged_absent_requirements_spine = Some refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        phase1_surface_tagged_present_empty_requirements_spine = Some refined.
Proof.
  intros [refined [Habsent Hpresent]].
  apply phase1_surface_tagged_requirements_presence_separated.
  eapply phase1_surface_recursive_grouping_tagged_admission_injective;
    eassumption.
Qed.
