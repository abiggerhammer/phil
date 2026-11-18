From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementRecursiveGroupingSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission.

(*
  Bounded G3: no selected parse tree can be admitted as both Record and
  Data. Root nonterminals remain source-owned, even if normalized outputs
  differ. Canonical grammar and TCB are unchanged. Publicly constructible
  carriers are never presumed valid.
*)

Theorem phase1_surface_recursive_grouping_record_data_same_tree_excluded :
  forall tree record data_value,
    phase1_surface_normalize_recursive_grouping_record_implementation tree =
      Some record ->
    phase1_surface_normalize_recursive_grouping_data_implementation tree =
      Some data_value ->
    False.
Proof.
  intros tree record data_value Hrecord Hdata.
  pose proof
    (phase1_surface_normalize_recursive_grouping_record_implementation_round_trip
      tree record Hrecord) as Hrecord_tree.
  pose proof
    (phase1_surface_normalize_recursive_grouping_data_implementation_round_trip
      tree data_value Hdata) as Hdata_tree.
  unfold phase1_surface_recursive_grouping_implementation_record_tree,
    phase1_surface_record_generic_requirement_recursive_grouping_spine_tree
    in Hrecord_tree.
  unfold phase1_surface_recursive_grouping_implementation_data_tree,
    phase1_surface_data_generic_requirement_recursive_grouping_spine_tree
    in Hdata_tree.
  rewrite <- Hrecord_tree in Hdata_tree.
  discriminate Hdata_tree.
Qed.

Theorem phase1_surface_recursive_grouping_data_tag_rejects_record_tree :
  forall tree record,
    phase1_surface_normalize_recursive_grouping_record_implementation tree =
      Some record ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros tree record Hrecord.
  change
    (match phase1_surface_normalize_recursive_grouping_data_implementation tree with
     | Some data_value =>
         Some (Phase1RecursiveGroupingImplementationDataDeclaration data_value)
     | None => None
     end = None).
  destruct (phase1_surface_normalize_recursive_grouping_data_implementation tree)
    as [data_value |] eqn:Hdata.
  - exfalso.
    eapply phase1_surface_recursive_grouping_record_data_same_tree_excluded;
      eassumption.
  - reflexivity.
Qed.

Theorem phase1_surface_recursive_grouping_record_tag_rejects_data_tree :
  forall tree data_value,
    phase1_surface_normalize_recursive_grouping_data_implementation tree =
      Some data_value ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros tree data_value Hdata.
  change
    (match phase1_surface_normalize_recursive_grouping_record_implementation tree with
     | Some record =>
         Some (Phase1RecursiveGroupingImplementationRecordDeclaration record)
     | None => None
     end = None).
  destruct (phase1_surface_normalize_recursive_grouping_record_implementation tree)
    as [record |] eqn:Hrecord.
  - exfalso.
    eapply phase1_surface_recursive_grouping_record_data_same_tree_excluded;
      eassumption.
  - reflexivity.
Qed.

Example phase1_surface_tagged_absent_requirements_same_tree_positive :
  phase1_surface_normalize_recursive_grouping_record_implementation
    (phase1_surface_recursive_grouping_implementation_record_tree
      phase1_surface_impl_absent_requirements_record) =
    Some phase1_surface_impl_absent_requirements_record.
Proof. exact phase1_surface_impl_absent_requirements_accepted. Qed.

Example phase1_surface_tagged_present_empty_requirements_same_tree_positive :
  phase1_surface_normalize_recursive_grouping_record_implementation
    (phase1_surface_recursive_grouping_implementation_record_tree
      phase1_surface_impl_present_empty_requirements_record) =
    Some phase1_surface_impl_present_empty_requirements_record.
Proof. exact phase1_surface_impl_present_empty_requirements_accepted. Qed.

Example phase1_surface_tagged_absent_requirements_wrong_data_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof.
  eapply phase1_surface_recursive_grouping_data_tag_rejects_record_tree.
  exact phase1_surface_impl_absent_requirements_accepted.
Qed.

Example phase1_surface_tagged_present_empty_requirements_wrong_data_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} = None.
Proof.
  eapply phase1_surface_recursive_grouping_data_tag_rejects_record_tree.
  exact phase1_surface_impl_present_empty_requirements_accepted.
Qed.
