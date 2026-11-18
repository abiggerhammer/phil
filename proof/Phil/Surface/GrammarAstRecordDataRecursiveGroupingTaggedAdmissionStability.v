From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingTaggedAdmissionInjectivity.

(*
  Bounded G3: admitted tagged declaration spines are stable under
  reconstruction and repeated admission.  These results are conditional on
  successful normalization; they DO NOT assert that arbitrary publicly
  constructible implementation carriers are valid.  Different Record/Data
  tags cannot be admitted to one result.  Source Grammar-v1, production
  parser binding and whole-source G2/G4 correspondence remain unchanged.
*)

Theorem phase1_surface_recursive_grouping_tagged_admission_replay :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
      = Some refined.
Proof.
  intros declaration refined Hnormalize.
  rewrite (phase1_surface_recursive_grouping_implementation_tagged_round_trip
    declaration refined Hnormalize).
  exact Hnormalize.
Qed.

Theorem phase1_surface_recursive_grouping_tagged_admission_replay_unique :
  forall declaration refined replayed,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine refined)
      = Some replayed ->
    refined = replayed.
Proof.
  intros declaration refined replayed Hnormalize Hreplay.
  rewrite (phase1_surface_recursive_grouping_implementation_tagged_round_trip
    declaration refined Hnormalize) in Hreplay.
  rewrite Hnormalize in Hreplay.
  injection Hreplay as Hequal.
  exact Hequal.
Qed.

Theorem phase1_surface_recursive_grouping_tagged_admission_cross_tag_exclusion :
  forall record data_value refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        (Phase1RecursiveGroupingImplementationRecordDeclaration record)) =
      Some refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        (Phase1RecursiveGroupingImplementationDataDeclaration data_value)) =
      Some refined ->
    False.
Proof.
  intros record data_value refined Hrecord Hdata.
  apply (phase1_surface_recursive_grouping_tagged_record_data_disjoint
    record data_value).
  eapply phase1_surface_recursive_grouping_tagged_admission_injective;
    eassumption.
Qed.

Example phase1_surface_tagged_absent_requirements_replay_stable :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_absent_requirements_record)) =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_absent_requirements_record).
Proof.
  eapply phase1_surface_recursive_grouping_tagged_admission_replay.
  exact phase1_surface_tagged_absent_requirements_still_accepted.
Qed.

Example phase1_surface_tagged_present_empty_requirements_replay_stable :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_present_empty_requirements_record)) =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_present_empty_requirements_record).
Proof.
  eapply phase1_surface_recursive_grouping_tagged_admission_replay.
  exact phase1_surface_tagged_present_empty_requirements_still_accepted.
Qed.
