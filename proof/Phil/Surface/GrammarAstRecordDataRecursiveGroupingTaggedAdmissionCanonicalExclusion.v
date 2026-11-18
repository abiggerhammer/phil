From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionSeparation.

Open Scope string_scope.

(*
  Bounded G3: a canonical record_decl or data_decl Derives witness
  guarantees admission under its own tag and rejection under the other.
  A single selected tree cannot have both canonical root derivations.
  No trust, Grammar-v1 change, production parser binding, G2/G4, or
  assertion of arbitrary intermediate-carrier validity is introduced.
*)

Theorem phase1_surface_certified_record_tags_exclusive :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    (exists refined,
       phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
         {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
            phase1_declaration_spine_selected_tree := tree |} = Some refined) /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_certified_record_has_recursive_grouping_implementation_view
      path input rest tree Hderive)
    as [record [Hnormalize _]].
  split.
  - exists (Phase1RecursiveGroupingImplementationRecordDeclaration record).
    cbn. now rewrite Hnormalize.
  - eapply phase1_surface_recursive_grouping_data_tag_rejects_record_tree.
    exact Hnormalize.
Qed.

Theorem phase1_surface_certified_data_tags_exclusive :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    (exists refined,
       phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
         {| phase1_declaration_spine_tag := Phase1DataDeclaration;
            phase1_declaration_spine_selected_tree := tree |} = Some refined) /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_certified_data_has_recursive_grouping_implementation_view
      path input rest tree Hderive)
    as [data_value [Hnormalize _]].
  split.
  - exists (Phase1RecursiveGroupingImplementationDataDeclaration data_value).
    cbn. now rewrite Hnormalize.
  - eapply phase1_surface_recursive_grouping_record_tag_rejects_data_tree.
    exact Hnormalize.
Qed.

Theorem phase1_surface_certified_record_data_root_trees_disjoint :
  forall record_path record_input record_rest
         data_path data_input data_rest tree,
    Derives phase1_surface_rules record_path
      (ENonterminal "record_decl") record_input record_rest tree ->
    Derives phase1_surface_rules data_path
      (ENonterminal "data_decl") data_input data_rest tree ->
    False.
Proof.
  intros record_path record_input record_rest
    data_path data_input data_rest tree Hrecord Hdata.
  destruct
    (phase1_surface_certified_record_has_recursive_grouping_implementation_view
      record_path record_input record_rest tree Hrecord)
    as [record [Hrecord_normalized _]].
  destruct
    (phase1_surface_certified_data_has_recursive_grouping_implementation_view
      data_path data_input data_rest tree Hdata)
    as [data_value [Hdata_normalized _]].
  eapply phase1_surface_recursive_grouping_record_data_same_tree_excluded;
    eassumption.
Qed.

Example phase1_surface_absent_requirements_tag_pair_control :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record) /\
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof.
  split.
  - exact phase1_surface_tagged_absent_requirements_record_accepted.
  - exact phase1_surface_tagged_absent_requirements_wrong_data_tag_rejected.
Qed.

Example phase1_surface_present_empty_requirements_tag_pair_control :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record) /\
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} = None.
Proof.
  split.
  - exact phase1_surface_tagged_present_empty_requirements_record_accepted.
  - exact phase1_surface_tagged_present_empty_requirements_wrong_data_tag_rejected.
Qed.
