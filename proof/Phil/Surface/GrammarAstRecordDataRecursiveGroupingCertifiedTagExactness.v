From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionCanonicalExclusion.

Open Scope string_scope.

(*
  Bounded G3: canonical record_decl and data_decl Derives witnesses
  determine the unique admissible tag among all fifteen top-level tags.
  This is a success iff statement and a fail-closed rejection statement
  for every nonmatching tag, not merely the opposite Record/Data tag.
  No claim is made that arbitrary publicly constructible selected trees
  are canonical, or that the production parser or G2/G4 are bound here.
*)

Theorem phase1_surface_certified_record_admission_tag_iff :
  forall path input rest tree tag,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    ((exists refined,
        phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
          {| phase1_declaration_spine_tag := tag;
             phase1_declaration_spine_selected_tree := tree |} = Some refined)
      <-> tag = Phase1RecordDeclaration).
Proof.
  intros path input rest tree tag Hderive.
  split.
  - intros [refined Hnormalize].
    destruct (phase1_surface_recursive_grouping_impl_admission_tag_sound
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |}
      refined Hnormalize) as [Hrecord | Hdata].
    + exact Hrecord.
    + cbn in Hdata. subst tag.
      destruct (phase1_surface_certified_record_tags_exclusive
        path input rest tree Hderive) as [_ Hreject].
      rewrite Hreject in Hnormalize.
      discriminate Hnormalize.
  - intro Htag. subst tag.
    destruct (phase1_surface_certified_record_tags_exclusive
      path input rest tree Hderive) as [[refined Hnormalize] _].
    exists refined. exact Hnormalize.
Qed.

Theorem phase1_surface_certified_data_admission_tag_iff :
  forall path input rest tree tag,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    ((exists refined,
        phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
          {| phase1_declaration_spine_tag := tag;
             phase1_declaration_spine_selected_tree := tree |} = Some refined)
      <-> tag = Phase1DataDeclaration).
Proof.
  intros path input rest tree tag Hderive.
  split.
  - intros [refined Hnormalize].
    destruct (phase1_surface_recursive_grouping_impl_admission_tag_sound
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |}
      refined Hnormalize) as [Hrecord | Hdata].
    + cbn in Hrecord. subst tag.
      destruct (phase1_surface_certified_data_tags_exclusive
        path input rest tree Hderive) as [_ Hreject].
      rewrite Hreject in Hnormalize.
      discriminate Hnormalize.
    + exact Hdata.
  - intro Htag. subst tag.
    destruct (phase1_surface_certified_data_tags_exclusive
      path input rest tree Hderive) as [[refined Hnormalize] _].
    exists refined. exact Hnormalize.
Qed.

Theorem phase1_surface_certified_record_nonmatching_tag_rejected :
  forall path input rest tree tag,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    tag <> Phase1RecordDeclaration ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros path input rest tree tag Hderive Hneq.
  destruct
    (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |})
    as [refined |] eqn:Hnormalize.
  - exfalso. apply Hneq.
    apply (proj1 (phase1_surface_certified_record_admission_tag_iff
      path input rest tree tag Hderive)).
    now exists refined.
  - reflexivity.
Qed.

Theorem phase1_surface_certified_data_nonmatching_tag_rejected :
  forall path input rest tree tag,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    tag <> Phase1DataDeclaration ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |} = None.
Proof.
  intros path input rest tree tag Hderive Hneq.
  destruct
    (phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := tag;
         phase1_declaration_spine_selected_tree := tree |})
    as [refined |] eqn:Hnormalize.
  - exfalso. apply Hneq.
    apply (proj1 (phase1_surface_certified_data_admission_tag_iff
      path input rest tree tag Hderive)).
    now exists refined.
  - reflexivity.
Qed.

Example phase1_surface_absent_requirements_exact_tag_positive :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record).
Proof. exact phase1_surface_tagged_absent_requirements_record_accepted. Qed.

Example phase1_surface_present_empty_requirements_exact_tag_positive :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} =
    Some (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).
Proof. exact phase1_surface_tagged_present_empty_requirements_record_accepted. Qed.

Example phase1_surface_absent_requirements_type_alias_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1TypeAliasDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof.
  eapply phase1_surface_recursive_grouping_impl_other_tags_rejected;
    discriminate.
Qed.

Example phase1_surface_present_empty_requirements_program_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1ProgramDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_present_empty_requirements_record |} = None.
Proof.
  eapply phase1_surface_recursive_grouping_impl_other_tags_rejected;
    discriminate.
Qed.
