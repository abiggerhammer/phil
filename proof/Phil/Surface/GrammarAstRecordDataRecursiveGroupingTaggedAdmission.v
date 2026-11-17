From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples.

Open Scope string_scope.

(*
  Bounded G3: the existing normalizer reconstructs a selected parse tree,
  but its public input also has a declaration tag.  Preserve both, including
  the match between the Record/Data tag and the admitted constructor.
  Only successful normalization and canonical Derives support these claims:
  arbitrary user-constructed implementation carriers are not asserted valid.
  No production Haskell parser or whole-source G2/G4 correspondence is claimed.
*)

Definition phase1_surface_recursive_grouping_implementation_declaration_spine
  (refined : Phase1SurfaceRecursiveGroupingImplementationRecordDataDeclaration)
  : Phase1SurfaceDeclarationSpine :=
  match refined with
  | Phase1RecursiveGroupingImplementationRecordDeclaration record =>
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree :=
           phase1_surface_recursive_grouping_implementation_record_tree record |}
  | Phase1RecursiveGroupingImplementationDataDeclaration data_value =>
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree :=
           phase1_surface_recursive_grouping_implementation_data_tree data_value |}
  end.

Theorem phase1_surface_recursive_grouping_implementation_tagged_round_trip :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_recursive_grouping_implementation_declaration_spine refined =
      declaration.
Proof.
  intros [tag tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_recursive_grouping_record_implementation tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_grouping_record_implementation_round_trip
        tree record Hrecord).
    reflexivity.
  - destruct
      (phase1_surface_normalize_recursive_grouping_data_implementation tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_recursive_grouping_data_implementation_round_trip
        tree data_value Hdata).
    reflexivity.
Qed.

Theorem phase1_surface_recursive_grouping_implementation_admission_tag_exact :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_declaration_spine_tag declaration =
      phase1_declaration_spine_tag
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          refined).
Proof.
  intros declaration refined Hnormalize.
  rewrite (phase1_surface_recursive_grouping_implementation_tagged_round_trip
    declaration refined Hnormalize).
  reflexivity.
Qed.

Theorem phase1_surface_certified_record_has_tagged_recursive_grouping_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_recursive_grouping_implementation_declaration_spine refined =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_record_has_recursive_grouping_implementation_view
    path input rest tree Hderive)
    as [record [Hnormalize Htree]].
  exists (Phase1RecursiveGroupingImplementationRecordDeclaration record).
  split.
  - cbn. now rewrite Hnormalize.
  - cbn. now rewrite Htree.
Qed.

Theorem phase1_surface_certified_data_has_tagged_recursive_grouping_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some refined /\
      phase1_surface_recursive_grouping_implementation_declaration_spine refined =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_data_has_recursive_grouping_implementation_view
    path input rest tree Hderive)
    as [data_value [Hnormalize Htree]].
  exists (Phase1RecursiveGroupingImplementationDataDeclaration data_value).
  split.
  - cbn. now rewrite Hnormalize.
  - cbn. now rewrite Htree.
Qed.

Example phase1_surface_tagged_absent_requirements_record_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record).
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_tagged_present_empty_requirements_record_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).
Proof. vm_compute. reflexivity. Qed.

Example phase1_surface_tagged_record_tree_under_data_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof. exact phase1_surface_impl_record_tree_under_data_tag_rejected. Qed.
