From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstGenericRequirementsRecursiveGroupingSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation.

Import ListNotations.
Open Scope string_scope.

(*
  Bounded G3 admission controls for the extracted record/data representation.
  They exercise public, constructible intermediate carriers, not only source
  Grammar-v1 derivations.  These tests do not bind the production Haskell parser
  and do not establish G2/G4 or whole-source correspondence.
*)

Definition phase1_surface_impl_absent_requirements_record
  : Phase1SurfaceRecursiveGroupingImplementationRecordDeclaration :=
  {| phase1_recursive_grouping_impl_record_name := "Guarded";
     phase1_recursive_grouping_impl_record_generic_params := None;
     phase1_recursive_grouping_impl_record_mode := None;
     phase1_recursive_grouping_impl_record_requirements := None;
     phase1_recursive_grouping_impl_record_fields := None |}.

Definition phase1_surface_impl_present_empty_requirements_record
  : Phase1SurfaceRecursiveGroupingImplementationRecordDeclaration :=
  {| phase1_recursive_grouping_impl_record_name := "Guarded";
     phase1_recursive_grouping_impl_record_generic_params := None;
     phase1_recursive_grouping_impl_record_mode := None;
     phase1_recursive_grouping_impl_record_requirements :=
       Some {| phase1_generic_requirements_recursive_grouping_spine_entries := [] |};
     phase1_recursive_grouping_impl_record_fields := None |}.

Example phase1_surface_impl_absent_requirements_accepted :
  phase1_surface_normalize_recursive_grouping_record_implementation
    (phase1_surface_recursive_grouping_implementation_record_tree
      phase1_surface_impl_absent_requirements_record) =
    Some phase1_surface_impl_absent_requirements_record.
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_impl_present_empty_requirements_accepted :
  phase1_surface_normalize_recursive_grouping_record_implementation
    (phase1_surface_recursive_grouping_implementation_record_tree
      phase1_surface_impl_present_empty_requirements_record) =
    Some phase1_surface_impl_present_empty_requirements_record.
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_impl_absent_and_present_empty_are_distinct :
  phase1_surface_recursive_grouping_implementation_record_tree
    phase1_surface_impl_absent_requirements_record <>
  phase1_surface_recursive_grouping_implementation_record_tree
    phase1_surface_impl_present_empty_requirements_record.
Proof.
  intro Hequal.
  vm_compute in Hequal.
  discriminate Hequal.
Qed.

Theorem phase1_surface_recursive_grouping_impl_other_tags_rejected :
  forall tag tree,
    tag <> Phase1RecordDeclaration ->
    tag <> Phase1DataDeclaration ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros tag tree Hrecord Hdata.
  destruct tag; cbn; try congruence; reflexivity.
Qed.

Theorem phase1_surface_recursive_grouping_impl_admission_tag_sound :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_declaration_spine_tag declaration = Phase1RecordDeclaration \/
    phase1_declaration_spine_tag declaration = Phase1DataDeclaration.
Proof.
  intros [tag tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize; auto.
Qed.

Example phase1_surface_impl_record_tree_under_data_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_impl_literal_under_record_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_impl_malformed_record_shell_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         PTNonterminal "record_decl" (PTSequence [PTLiteral "data"]) |} = None.
Proof. vm_compute. reflexivity. Qed.
