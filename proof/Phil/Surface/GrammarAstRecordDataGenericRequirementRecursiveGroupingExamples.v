From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordDataGenericRequirementPropositionSpine
  GrammarAstRecordDataGenericRequirementRecursiveGroupingSpine
  GrammarAstRecordDataGenericRequirementRecursiveGroupingTotality
  GrammarAstGenericRequirementsPropositionSpine
  GrammarAstGenericRequirementsRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* Declaration-level negative/positive controls for optional requirements.
   These preserve the syntax shell and every unrelated declaration field. *)

Definition phase1_record_grouping_absent_source
  : Phase1SurfaceRecordGenericRequirementPropositionSpine :=
  {| phase1_record_generic_requirement_proposition_spine_name := "Example";
     phase1_record_generic_requirement_proposition_spine_generic_params := None;
     phase1_record_generic_requirement_proposition_spine_mode := None;
     phase1_record_generic_requirement_proposition_spine_requirements := None;
     phase1_record_generic_requirement_proposition_spine_fields := None |}.

Definition phase1_record_grouping_present_empty_source
  : Phase1SurfaceRecordGenericRequirementPropositionSpine :=
  {| phase1_record_generic_requirement_proposition_spine_name := "Example";
     phase1_record_generic_requirement_proposition_spine_generic_params := None;
     phase1_record_generic_requirement_proposition_spine_mode := None;
     phase1_record_generic_requirement_proposition_spine_requirements :=
       Some {| phase1_generic_requirements_proposition_spine_entries := [] |};
     phase1_record_generic_requirement_proposition_spine_fields := None |}.

Example phase1_record_grouping_absent_stays_absent :
  match phase1_surface_normalize_record_generic_requirement_recursive_grouping_spine
    phase1_record_grouping_absent_source with
  | Some record =>
      phase1_record_generic_requirement_recursive_grouping_spine_requirements record =
        None /\
      phase1_surface_record_generic_requirement_recursive_grouping_spine_tree record =
        phase1_surface_record_generic_requirement_proposition_spine_tree
          phase1_record_grouping_absent_source
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_record_grouping_present_empty_stays_present :
  match phase1_surface_normalize_record_generic_requirement_recursive_grouping_spine
    phase1_record_grouping_present_empty_source with
  | Some record =>
      phase1_record_generic_requirement_recursive_grouping_spine_requirements record =
        Some {| phase1_generic_requirements_recursive_grouping_spine_entries := [] |} /\
      phase1_surface_record_generic_requirement_recursive_grouping_spine_tree record =
        phase1_surface_record_generic_requirement_proposition_spine_tree
          phase1_record_grouping_present_empty_source
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example phase1_data_grouping_preserves_entire_tree :
  forall base refined,
    phase1_surface_normalize_data_generic_requirement_recursive_grouping_spine base =
      Some refined ->
    phase1_surface_data_generic_requirement_recursive_grouping_spine_tree refined =
      phase1_surface_data_generic_requirement_proposition_spine_tree base.
Proof.
  intros base refined Hnormalize.
  eapply phase1_surface_normalize_data_generic_requirement_recursive_grouping_spine_round_trip.
  exact Hnormalize.
Qed.
