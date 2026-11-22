From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationReplayPairCoherence.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: a compositional three-key
  observation-replay chain. All three normalizations must actually
  succeed. A pair of replayed observational relations composes to
  an outer relation, carrying certificate membership and declaration
  family tags while excluding incompatible certificates.

  This is a bounded triple replay corollary of the established
  observation PER and pair-replay laws, not a claim of exact key
  equality, a Grammar-v1/TCB change, production AST binding, G2/G4
  completion or Phase 1 closure.
*)

Theorem phase1_surface_triple_replay_chain_transitive :
  forall left middle right left_refined middle_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      middle = Some middle_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined).
Proof.
  intros left middle right left_refined middle_refined right_refined
    Hleft Hmiddle Hright Hlm Hmr.
  apply (proj2 (phase1_surface_dual_replay_related_iff_original
    left right left_refined right_refined Hleft Hright)).
  eapply phase1_surface_recursive_grouping_observation_related_transitive.
  - apply (proj1 (phase1_surface_dual_replay_related_iff_original
      left middle left_refined middle_refined Hleft Hmiddle)).
    exact Hlm.
  - apply (proj1 (phase1_surface_dual_replay_related_iff_original
      middle right middle_refined right_refined Hmiddle Hright)).
    exact Hmr.
Qed.

Theorem phase1_surface_triple_replay_certificate_fiber_transport :
  forall left middle right left_refined middle_refined right_refined
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      middle = Some middle_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_admitted_observation_key entry) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined)
      (phase1_admitted_observation_key entry).
Proof.
  intros left middle right left_refined middle_refined right_refined
    entry Hleft Hmiddle Hright Hlm Hmr Hmember.
  pose proof (phase1_surface_triple_replay_chain_transitive
    left middle right left_refined middle_refined right_refined
    Hleft Hmiddle Hright Hlm Hmr) as Hchain.
  eapply phase1_surface_recursive_grouping_observation_related_transitive.
  - apply phase1_surface_recursive_grouping_observation_related_symmetric.
    exact Hchain.
  - exact Hmember.
Qed.

Theorem phase1_surface_triple_replay_chain_preserves_tag :
  forall left middle right left_refined middle_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      middle = Some middle_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined) ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left middle right left_refined middle_refined right_refined
    Hleft Hmiddle Hright Hlm Hmr.
  apply (phase1_surface_dual_replay_related_preserves_tag
    left right left_refined right_refined Hleft Hright).
  exact (phase1_surface_triple_replay_chain_transitive
    left middle right left_refined middle_refined right_refined
    Hleft Hmiddle Hright Hlm Hmr).
Qed.

Theorem phase1_surface_triple_replay_distinct_certificates_separated :
  forall left middle right left_refined middle_refined right_refined
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      middle = Some middle_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        middle_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined) ->
    phase1_surface_admitted_observation first <>
      phase1_surface_admitted_observation second ->
    ~ (phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           left_refined)
         (phase1_admitted_observation_key first) /\
       phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           right_refined)
         (phase1_admitted_observation_key second)).
Proof.
  intros left middle right left_refined middle_refined right_refined
    first second Hleft Hmiddle Hright Hlm Hmr Hdistinct
    [Hfirst Hsecond].
  pose proof (phase1_surface_triple_replay_chain_transitive
    left middle right left_refined middle_refined right_refined
    Hleft Hmiddle Hright Hlm Hmr) as Hchain.
  apply (phase1_surface_dual_replay_distinct_certificates_separated
    left right left_refined right_refined first second
    Hleft Hright Hdistinct).
  repeat split; assumption.
Qed.

Example phase1_surface_triple_replay_malformed_record_excluded :
  forall middle_refined right_refined,
    ~ (phase1_surface_recursive_grouping_observation_related
         {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
            phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           middle_refined) /\
       phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           middle_refined)
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           right_refined)).
Proof.
  intros middle_refined right_refined [Hmalformed _].
  apply (phase1_surface_dual_replay_rejected_record_excluded middle_refined).
  exact Hmalformed.
Qed.
