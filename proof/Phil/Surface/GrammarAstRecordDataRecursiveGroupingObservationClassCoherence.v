From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedDerivations.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: observation classes of canonical
  Grammar-v1 Record/Data declarations are independent of the chosen
  successful admission certificate. A class is not an exact public
  tag/tree identity: observation equality may lose source distinctions.
  Record and Data derived classes remain disjoint.

  This is a proof-side class-coherence result, not a production parser
  or AST binding, G2/G4 correspondence, or Phase 1 closure. It neither
  broadens public admission nor changes Grammar-v1 or the TCB.
*)

Theorem phase1_surface_admitted_observation_class_coherence :
  forall left left' right right' : Phase1SurfaceAdmittedObservationKey,
    phase1_admitted_observation_key left =
      phase1_admitted_observation_key left' ->
    phase1_admitted_observation_key right =
      phase1_admitted_observation_key right' ->
    phase1_surface_admitted_observation_equiv left right ->
    phase1_surface_admitted_observation_equiv left' right'.
Proof.
  intros left left' right right' Hleft Hright Hequiv.
  eapply phase1_surface_admitted_observation_equiv_transitive
    with (middle := left).
  - apply phase1_surface_admitted_observation_same_key_equiv.
    symmetry.
    exact Hleft.
  - eapply phase1_surface_admitted_observation_equiv_transitive
      with (middle := right).
    + exact Hequiv.
    + apply phase1_surface_admitted_observation_same_key_equiv.
      exact Hright.
Qed.

Theorem phase1_surface_derived_record_class_witness_independent :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists chosen : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key chosen =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      forall other : Phase1SurfaceAdmittedObservationKey,
        phase1_admitted_observation_key other =
          {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
             phase1_declaration_spine_selected_tree := tree |} ->
        phase1_surface_admitted_observation_equiv other chosen.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_has_admitted_equivalence_representative
    path input rest tree Hderive) as [chosen [Hchosen _]].
  exists chosen.
  split; [exact Hchosen |].
  intros other Hother.
  apply phase1_surface_admitted_observation_same_key_equiv.
  rewrite Hother, Hchosen.
  reflexivity.
Qed.

Theorem phase1_surface_derived_data_class_witness_independent :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists chosen : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key chosen =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} /\
      forall other : Phase1SurfaceAdmittedObservationKey,
        phase1_admitted_observation_key other =
          {| phase1_declaration_spine_tag := Phase1DataDeclaration;
             phase1_declaration_spine_selected_tree := tree |} ->
        phase1_surface_admitted_observation_equiv other chosen.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_has_admitted_equivalence_representative
    path input rest tree Hderive) as [chosen [Hchosen _]].
  exists chosen.
  split; [exact Hchosen |].
  intros other Hother.
  apply phase1_surface_admitted_observation_same_key_equiv.
  rewrite Hother, Hchosen.
  reflexivity.
Qed.

Theorem phase1_surface_derived_record_data_classes_disjoint :
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
      ~ phase1_surface_admitted_observation_equiv record_entry data_entry.
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
  apply phase1_surface_admitted_record_data_equivalence_classes_disjoint.
  - rewrite Hrecord_key.
    reflexivity.
  - rewrite Hdata_key.
    reflexivity.
Qed.
