From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity
  GrammarAstRecordDataRecursiveGroupingCertifiedTagExactness.

Open Scope string_scope.

(*
  Bounded G3: canonical Record/Data Derives witnesses determine a
  single admitted implementation value and an exact tagged-tree
  reconstruction. Independently certified Record and Data roots never
  share that implementation value. These claims use canonical Derives
  and successful tagged normalization; arbitrary publicly constructible
  carriers are not assumed valid. No production binding or G2/G4 claim.
*)

Theorem phase1_surface_certified_record_admission_fiber_singleton :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_recursive_grouping_implementation_declaration_spine refined =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      (forall candidate,
        phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
          {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
             phase1_declaration_spine_selected_tree := tree |} = Some candidate ->
        candidate = refined).
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_record_has_tagged_recursive_grouping_view
    path input rest tree Hderive) as [refined [Hnormalize Hreconstruct]].
  exists refined.
  split; [exact Hnormalize |].
  split; [exact Hreconstruct |].
  intros candidate Hcandidate.
  rewrite Hnormalize in Hcandidate.
  inversion Hcandidate.
  reflexivity.
Qed.

Theorem phase1_surface_certified_data_admission_fiber_singleton :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_recursive_grouping_implementation_declaration_spine refined =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      (forall candidate,
        phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
          {| phase1_declaration_spine_tag := Phase1DataDeclaration;
             phase1_declaration_spine_selected_tree := tree |} = Some candidate ->
        candidate = refined).
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_data_has_tagged_recursive_grouping_view
    path input rest tree Hderive) as [refined [Hnormalize Hreconstruct]].
  exists refined.
  split; [exact Hnormalize |].
  split; [exact Hreconstruct |].
  intros candidate Hcandidate.
  rewrite Hnormalize in Hcandidate.
  inversion Hcandidate.
  reflexivity.
Qed.

Theorem phase1_surface_certified_record_data_admission_fibers_disjoint :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree,
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    exists record_refined data_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |} =
        Some record_refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |} =
        Some data_refined /\
      record_refined <> data_refined.
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree Hrecord Hdata.
  destruct (phase1_surface_certified_record_has_tagged_recursive_grouping_view
    record_path record_input record_rest record_tree Hrecord)
    as [record_refined [Hrecord_normalize Hrecord_reconstruct]].
  destruct (phase1_surface_certified_data_has_tagged_recursive_grouping_view
    data_path data_input data_rest data_tree Hdata)
    as [data_refined [Hdata_normalize Hdata_reconstruct]].
  exists record_refined, data_refined.
  split; [exact Hrecord_normalize |].
  split; [exact Hdata_normalize |].
  intro Hequal.
  rewrite <- Hequal in Hdata_reconstruct.
  rewrite Hrecord_reconstruct in Hdata_reconstruct.
  discriminate Hdata_reconstruct.
Qed.

Example phase1_surface_absent_requirements_admission_value_unique :
  forall candidate,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_absent_requirements_spine = Some candidate ->
    candidate = Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record.
Proof.
  intros candidate Hcandidate.
  rewrite phase1_surface_tagged_absent_requirements_still_accepted in Hcandidate.
  inversion Hcandidate.
  reflexivity.
Qed.

Example phase1_surface_present_empty_requirements_admission_value_unique :
  forall candidate,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_present_empty_requirements_spine = Some candidate ->
    candidate = Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record.
Proof.
  intros candidate Hcandidate.
  rewrite phase1_surface_tagged_present_empty_requirements_still_accepted in Hcandidate.
  inversion Hcandidate.
  reflexivity.
Qed.

Example phase1_surface_distinct_requirements_fibers_do_not_collapse :
  ~ exists refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_absent_requirements_spine = Some refined /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      phase1_surface_tagged_present_empty_requirements_spine = Some refined.
Proof.
  exact phase1_surface_tagged_requirements_presence_not_collapsed.
Qed.
