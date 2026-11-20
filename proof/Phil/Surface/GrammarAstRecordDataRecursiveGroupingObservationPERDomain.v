From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingDerivedObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: Record/Data observation-PER support is
  exactly successful public-key admission. Rejected keys cannot enter
  any observation class. Canonical Grammar-v1 Record/Data derivations
  lie in disjoint observation classes. This is proof-side only: no
  production Haskell AST binding, G2/G4, or Phase 1 closure.
*)

Theorem phase1_surface_recursive_grouping_observation_support_iff_admission :
  forall declaration,
    phase1_surface_recursive_grouping_observation_related
      declaration declaration <->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        declaration = Some refined.
Proof.
  intros declaration.
  split.
  - intros [left_refined [right_refined [Hleft [_ _]]]].
    exists left_refined.
    exact Hleft.
  - intros [refined Hadmit].
    eapply phase1_surface_recursive_grouping_observation_related_reflexive_on_admission.
    exact Hadmit.
Qed.

Theorem phase1_surface_recursive_grouping_observation_related_has_admitted_endpoints :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right ->
    (exists left_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        left = Some left_refined) /\
    (exists right_refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        right = Some right_refined).
Proof.
  intros left right
    [left_refined [right_refined [Hleft [Hright _]]]].
  split.
  - exists left_refined. exact Hleft.
  - exists right_refined. exact Hright.
Qed.

Theorem phase1_surface_recursive_grouping_rejected_key_unrelated :
  forall rejected other,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      rejected = None ->
    ~ phase1_surface_recursive_grouping_observation_related rejected other.
Proof.
  intros rejected other Hreject
    [left_refined [right_refined [Hleft _]]].
  rewrite Hreject in Hleft.
  discriminate Hleft.
Qed.

Theorem phase1_surface_recursive_grouping_derived_record_in_observation_support :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |}
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_has_admitted_observation
    path input rest tree Hderive)
    as [refined [observed [Hadmit _]]].
  eapply phase1_surface_recursive_grouping_observation_related_reflexive_on_admission.
  exact Hadmit.
Qed.

Theorem phase1_surface_recursive_grouping_derived_data_in_observation_support :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_has_admitted_observation
    path input rest tree Hderive)
    as [refined [observed [Hadmit _]]].
  eapply phase1_surface_recursive_grouping_observation_related_reflexive_on_admission.
  exact Hadmit.
Qed.

Theorem phase1_surface_recursive_grouping_record_data_observation_classes_disjoint :
  forall record_tree data_tree,
    ~ phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |}
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |}.
Proof.
  intros record_tree data_tree Hrelated.
  pose proof
    (phase1_surface_recursive_grouping_observation_related_preserves_tag
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := record_tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := data_tree |}
      Hrelated) as Htag.
  simpl in Htag.
  discriminate Htag.
Qed.
