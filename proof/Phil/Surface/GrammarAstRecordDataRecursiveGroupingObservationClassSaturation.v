From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedDerivations
  GrammarAstRecordDataRecursiveGroupingObservationClassCoherence.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: public observational relatedness
  is exactly a *nonvacuous*, certificate-independent equality of admitted
  observation classes. Canonical Record/Data derivations admit witnesses
  whose entire classes remain separate for every certificate choice.

  These are proof-side consequences of already admitted observations,
  not exact public-key equality, new parser admission, production AST
  binding, G2/G4 correspondence, a TCB change, or Phase 1 closure.
*)

Theorem phase1_surface_public_observation_related_iff_all_certified_members :
  forall left right,
    phase1_surface_recursive_grouping_observation_related left right <->
    (exists chosen_left chosen_right : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key chosen_left = left /\
      phase1_admitted_observation_key chosen_right = right /\
      forall left_member right_member : Phase1SurfaceAdmittedObservationKey,
        phase1_admitted_observation_key left_member = left ->
        phase1_admitted_observation_key right_member = right ->
        phase1_surface_admitted_observation_equiv left_member right_member).
Proof.
  intros left right.
  split.
  - intros Hrelated.
    destruct (phase1_surface_public_related_has_admitted_observation_representatives
      left right Hrelated) as [chosen_left [chosen_right
        [Hleft [Hright Hequiv]]]].
    exists chosen_left, chosen_right.
    split; [exact Hleft |].
    split; [exact Hright |].
    intros left_member right_member Hleft_member Hright_member.
    eapply phase1_surface_admitted_observation_class_coherence
      with (left := chosen_left) (right := chosen_right).
    + rewrite Hleft, Hleft_member.
      reflexivity.
    + rewrite Hright, Hright_member.
      reflexivity.
    + exact Hequiv.
  - intros [chosen_left [chosen_right [Hleft [Hright Hall]]]].
    pose proof (Hall chosen_left chosen_right Hleft Hright) as Hequiv.
    apply (proj1 (phase1_surface_admitted_observation_equiv_iff_public_related
      chosen_left chosen_right)) in Hequiv.
    rewrite Hleft, Hright in Hequiv.
    exact Hequiv.
Qed.

Theorem phase1_surface_derived_record_data_all_certificates_separate :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree,
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    exists record_entry data_entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key record_entry =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |} /\
      phase1_admitted_observation_key data_entry =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |} /\
      forall record_choice data_choice : Phase1SurfaceAdmittedObservationKey,
        phase1_admitted_observation_key record_choice =
          {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
             phase1_declaration_spine_selected_tree := record_tree |} ->
        phase1_admitted_observation_key data_choice =
          {| phase1_declaration_spine_tag := Phase1DataDeclaration;
             phase1_declaration_spine_selected_tree := data_tree |} ->
        ~ phase1_surface_admitted_observation_equiv record_choice data_choice.
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree Hrecord Hdata.
  destruct (phase1_surface_derived_record_has_admitted_equivalence_representative
    record_path record_input record_rest record_tree Hrecord)
    as [record_entry [Hrecord_key _]].
  destruct (phase1_surface_derived_data_has_admitted_equivalence_representative
    data_path data_input data_rest data_tree Hdata)
    as [data_entry [Hdata_key _]].
  exists record_entry, data_entry.
  split; [exact Hrecord_key |].
  split; [exact Hdata_key |].
  intros record_choice data_choice Hrecord_choice Hdata_choice.
  apply (phase1_surface_admitted_record_data_equivalence_classes_disjoint
    record_choice data_choice).
  - rewrite Hrecord_choice.
    reflexivity.
  - rewrite Hdata_choice.
    reflexivity.
Qed.
