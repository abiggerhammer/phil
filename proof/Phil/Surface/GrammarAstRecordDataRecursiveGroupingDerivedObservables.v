From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables.

Open Scope string_scope.

(*
  Bounded PHIL-SURFACE-GRAMMAR-CORR-001 G3 continuation:
  canonical Grammar-v1 Record/Data derivations admit a
  production-observable *projection* of their exact retained carrier.
  The public tag and exact selected tree are retained by admission.
  The observable view remains lossy and is not a proof that Phil's
  production Haskell parser or AST implements this projection.

  Malformed public intermediate carriers remain rejected, even when
  a constructor/tag looks plausible. No new assumptions, Grammar-v1
  changes, G2/G4, or Phase 1 closure claims.
*)

Theorem phase1_surface_derived_record_has_admitted_observation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists refined observed,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} =
        Some refined /\
      observed = phase1_surface_observe_recursive_grouping_record_data refined /\
      phase1_surface_recursive_grouping_observed_tag observed =
        Phase1RecordDeclaration /\
      phase1_surface_recursive_grouping_implementation_declaration_spine
        refined =
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_record_has_tagged_recursive_grouping_view
    path input rest tree Hderive) as [refined [Hnormalize Hkey]].
  exists refined, (phase1_surface_observe_recursive_grouping_record_data refined).
  split; [exact Hnormalize |].
  split; [reflexivity |].
  split.
  - exact (phase1_surface_recursive_grouping_observation_admitted_tag_exact
      _ _ Hnormalize).
  - exact Hkey.
Qed.

Theorem phase1_surface_derived_data_has_admitted_observation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists refined observed,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} =
        Some refined /\
      observed = phase1_surface_observe_recursive_grouping_record_data refined /\
      phase1_surface_recursive_grouping_observed_tag observed =
        Phase1DataDeclaration /\
      phase1_surface_recursive_grouping_implementation_declaration_spine
        refined =
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |}.
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_certified_data_has_tagged_recursive_grouping_view
    path input rest tree Hderive) as [refined [Hnormalize Hkey]].
  exists refined, (phase1_surface_observe_recursive_grouping_record_data refined).
  split; [exact Hnormalize |].
  split; [reflexivity |].
  split.
  - exact (phase1_surface_recursive_grouping_observation_admitted_tag_exact
      _ _ Hnormalize).
  - exact Hkey.
Qed.

Example phase1_surface_derived_observation_malformed_record_literal_rejected :
  forall refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      <> Some refined.
Proof.
  intros refined Hnormalize.
  rewrite phase1_surface_impl_literal_under_record_tag_rejected in Hnormalize.
  discriminate Hnormalize.
Qed.

Example phase1_surface_derived_observation_wrong_data_tag_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree :=
         phase1_surface_recursive_grouping_implementation_record_tree
           phase1_surface_impl_absent_requirements_record |} = None.
Proof.
  exact phase1_surface_impl_record_tree_under_data_tag_rejected.
Qed.
