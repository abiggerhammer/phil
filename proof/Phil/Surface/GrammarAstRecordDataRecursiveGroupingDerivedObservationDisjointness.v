From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingDerivedObservables
  GrammarAstRecordDataRecursiveGroupingObservationSeparation.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: ground Record/Data observable-family
  separation in two canonical Grammar-v1 derivations and successful
  exact-key admission witnesses. The projection is lossy. This is a
  bounded proof-side result, not a production Haskell parser/AST binding,
  G2/G4 proof, or Phase 1 closure.
*)

Theorem phase1_surface_certified_record_data_observations_separated :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree,
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    exists record_refined data_refined record_observed data_observed,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |} =
        Some record_refined /\
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |} =
        Some data_refined /\
      record_observed =
        phase1_surface_observe_recursive_grouping_record_data record_refined /\
      data_observed =
        phase1_surface_observe_recursive_grouping_record_data data_refined /\
      record_observed <> data_observed /\
      phase1_surface_recursive_grouping_implementation_declaration_spine
        record_refined =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |} /\
      phase1_surface_recursive_grouping_implementation_declaration_spine
        data_refined =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |}.
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree Hrecord Hdata.
  destruct (phase1_surface_derived_record_has_admitted_observation
    record_path record_input record_rest record_tree Hrecord)
    as [record_refined [record_observed
      [Hrecord_admit [Hrecord_observed [_ Hrecord_key]]]]].
  destruct (phase1_surface_derived_data_has_admitted_observation
    data_path data_input data_rest data_tree Hdata)
    as [data_refined [data_observed
      [Hdata_admit [Hdata_observed [_ Hdata_key]]]]].
  exists record_refined, data_refined, record_observed, data_observed.
  split; [exact Hrecord_admit |].
  split; [exact Hdata_admit |].
  split; [exact Hrecord_observed |].
  split; [exact Hdata_observed |].
  split.
  - rewrite Hrecord_observed, Hdata_observed.
    exact
      (phase1_surface_admitted_record_data_observations_disjoint
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |}
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |}
        record_refined data_refined Hrecord_admit Hdata_admit
        eq_refl eq_refl).
  - split; [exact Hrecord_key | exact Hdata_key].
Qed.
