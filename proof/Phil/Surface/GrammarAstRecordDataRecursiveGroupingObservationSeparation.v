From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingAcceptedKeyExtensionality
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingDerivedObservables.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: classify the admitted, lossy
  production-observable Record/Data projection without treating it as an
  injective admission key.

  Equality of admitted observations preserves the declaration family,
  but it does NOT imply equality of the exact public tag/tree key.
  The positive collision is certified by two actual successful admissions,
  not arbitrary malformed intermediate carriers. This remains proof-side;
  it does not bind a production Haskell parser/AST, prove G2/G4, or certify
  Phase 1 closure.
*)

Theorem phase1_surface_admitted_observation_equality_preserves_tag :
  forall left right left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_observe_recursive_grouping_record_data left_refined =
      phase1_surface_observe_recursive_grouping_record_data right_refined ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right left_refined right_refined Hleft Hright Hobserved.
  pose proof
    (f_equal phase1_surface_recursive_grouping_observed_tag Hobserved)
    as Htag.
  rewrite
    (phase1_surface_recursive_grouping_observation_admitted_tag_exact
      left left_refined Hleft) in Htag.
  rewrite
    (phase1_surface_recursive_grouping_observation_admitted_tag_exact
      right right_refined Hright) in Htag.
  exact Htag.
Qed.

Theorem phase1_surface_admitted_record_data_observations_disjoint :
  forall left right left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_declaration_spine_tag left = Phase1RecordDeclaration ->
    phase1_declaration_spine_tag right = Phase1DataDeclaration ->
    phase1_surface_observe_recursive_grouping_record_data left_refined <>
      phase1_surface_observe_recursive_grouping_record_data right_refined.
Proof.
  intros left right left_refined right_refined
    Hleft Hright Hrecord Hdata Hobserved.
  pose proof
    (phase1_surface_admitted_observation_equality_preserves_tag
      left right left_refined right_refined Hleft Hright Hobserved)
    as Htag.
  rewrite Hrecord, Hdata in Htag.
  discriminate Htag.
Qed.

Theorem phase1_surface_admitted_observation_collides_on_distinct_exact_keys :
  exists left right,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left) = Some left /\
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right) = Some right /\
    phase1_surface_observe_recursive_grouping_record_data left =
      phase1_surface_observe_recursive_grouping_record_data right /\
    phase1_surface_recursive_grouping_implementation_declaration_spine left <>
      phase1_surface_recursive_grouping_implementation_declaration_spine right.
Proof.
  exists
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record),
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).
  repeat split.
  - exact phase1_surface_accepted_key_absent_requirements_stable.
  - exact phase1_surface_accepted_key_present_empty_requirements_stable.
  - exact phase1_surface_recursive_grouping_observation_absent_empty_collapse.
  - intro Hkey.
    apply phase1_surface_impl_absent_and_present_empty_are_distinct.
    exact (f_equal phase1_declaration_spine_selected_tree Hkey).
Qed.

Example phase1_surface_observation_separation_wrong_tag_rejected :
  forall refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree :=
           phase1_surface_recursive_grouping_implementation_record_tree
             phase1_surface_impl_absent_requirements_record |}
      <> Some refined.
Proof.
  intros refined Hnormalize.
  rewrite phase1_surface_impl_record_tree_under_data_tag_rejected in Hnormalize.
  discriminate Hnormalize.
Qed.
