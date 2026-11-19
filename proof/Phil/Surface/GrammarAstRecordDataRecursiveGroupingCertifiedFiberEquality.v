From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity
  GrammarAstRecordDataRecursiveGroupingCertifiedAdmissionFibers.

Open Scope string_scope.

(*
  Bounded G3: canonical Record/Data root derivations determine admitted
  implementation values whose equality holds exactly when their original
  selected parse trees agree. This composes certified singleton admission,
  exact tagged reconstruction, and deterministic normalization. It does not
  assert validity of arbitrary public carriers or bind the production parser,
  G2/G4, or whole-source correspondence. Absent and present-empty generic
  requirements remain different admitted values.
*)

Theorem phase1_surface_certified_record_root_fiber_equality_iff :
  forall left_path left_input left_rest left_tree
         right_path right_input right_rest right_tree,
    Derives phase1_surface_rules left_path (ENonterminal "record_decl")
      left_input left_rest left_tree ->
    Derives phase1_surface_rules right_path (ENonterminal "record_decl")
      right_input right_rest right_tree ->
    exists left_refined right_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |} =
        Some left_refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} =
        Some right_refined /\
      (left_refined = right_refined <-> left_tree = right_tree).
Proof.
  intros left_path left_input left_rest left_tree
    right_path right_input right_rest right_tree Hleft Hright.
  destruct (phase1_surface_certified_record_admission_fiber_singleton
    left_path left_input left_rest left_tree Hleft)
    as [left_refined [Hleft_normalize [Hleft_reconstruct _]]].
  destruct (phase1_surface_certified_record_admission_fiber_singleton
    right_path right_input right_rest right_tree Hright)
    as [right_refined [Hright_normalize [Hright_reconstruct _]]].
  exists left_refined, right_refined.
  split; [exact Hleft_normalize |].
  split; [exact Hright_normalize |].
  split.
  - intro Hequal.
    rewrite Hequal in Hleft_reconstruct.
    rewrite Hright_reconstruct in Hleft_reconstruct.
    symmetry.
    exact (f_equal phase1_declaration_spine_selected_tree Hleft_reconstruct).
  - intro Htrees.
    subst right_tree.
    rewrite Hleft_normalize in Hright_normalize.
    now inversion Hright_normalize.
Qed.

Theorem phase1_surface_certified_data_root_fiber_equality_iff :
  forall left_path left_input left_rest left_tree
         right_path right_input right_rest right_tree,
    Derives phase1_surface_rules left_path (ENonterminal "data_decl")
      left_input left_rest left_tree ->
    Derives phase1_surface_rules right_path (ENonterminal "data_decl")
      right_input right_rest right_tree ->
    exists left_refined right_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |} =
        Some left_refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} =
        Some right_refined /\
      (left_refined = right_refined <-> left_tree = right_tree).
Proof.
  intros left_path left_input left_rest left_tree
    right_path right_input right_rest right_tree Hleft Hright.
  destruct (phase1_surface_certified_data_admission_fiber_singleton
    left_path left_input left_rest left_tree Hleft)
    as [left_refined [Hleft_normalize [Hleft_reconstruct _]]].
  destruct (phase1_surface_certified_data_admission_fiber_singleton
    right_path right_input right_rest right_tree Hright)
    as [right_refined [Hright_normalize [Hright_reconstruct _]]].
  exists left_refined, right_refined.
  split; [exact Hleft_normalize |].
  split; [exact Hright_normalize |].
  split.
  - intro Hequal.
    rewrite Hequal in Hleft_reconstruct.
    rewrite Hright_reconstruct in Hleft_reconstruct.
    symmetry.
    exact (f_equal phase1_declaration_spine_selected_tree Hleft_reconstruct).
  - intro Htrees.
    subst right_tree.
    rewrite Hleft_normalize in Hright_normalize.
    now inversion Hright_normalize.
Qed.

Example phase1_surface_absent_present_empty_fiber_values_remain_unequal :
  forall absent_value present_empty_value,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_absent_requirements_spine = Some absent_value ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_present_empty_requirements_spine =
        Some present_empty_value ->
    absent_value <> present_empty_value.
Proof.
  intros absent_value present_empty_value Habsent Hpresent Hequal.
  apply phase1_surface_tagged_requirements_presence_not_collapsed.
  exists absent_value.
  split; [exact Habsent |].
  now rewrite <- Hequal in Hpresent.
Qed.

Example phase1_surface_wrong_literal_record_fiber_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof.
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
