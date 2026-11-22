From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationCertificateFiberLaws
  GrammarAstRecordDataRecursiveGroupingObservationAdmissionReplay
  GrammarAstRecordDataRecursiveGroupingObservationReplayFiberTransport.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: two independently admitted
  Record/Data public keys may be replayed together without changing
  their observational equivalence, either fiber's certificate members,
  or their declaration-family boundary. A shared certificate forces
  equality of observations; incompatible certificates cannot be
  assigned to a related pair of replayed keys.

  The positive laws require two actual successful normalizations.
  The negative control rejects an ill-tagged public carrier, even
  against a reconstructed implementation declaration. Nothing here
  equates observation equality with exact key equality, alters the
  grammar/TCB, binds the production Haskell AST, or closes G2/G4.
*)

Theorem phase1_surface_dual_replay_related_iff_original :
  forall left right left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         left_refined)
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         right_refined) <->
     phase1_surface_recursive_grouping_observation_related left right).
Proof.
  intros left right left_refined right_refined Hleft Hright.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    left left_refined Hleft).
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    right right_refined Hright).
  tauto.
Qed.

Theorem phase1_surface_dual_replay_related_iff_observations :
  forall left right left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         left_refined)
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         right_refined) <->
     phase1_surface_observe_recursive_grouping_record_data left_refined =
       phase1_surface_observe_recursive_grouping_record_data right_refined).
Proof.
  intros left right left_refined right_refined Hleft Hright.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    left left_refined Hleft).
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    right right_refined Hright).
  split.
  - intros [left' [right' [Hleft' [Hright' Hobserved]]]].
    rewrite Hleft in Hleft'.
    inversion Hleft'; subst left'.
    rewrite Hright in Hright'.
    inversion Hright'; subst right'.
    exact Hobserved.
  - intro Hobserved.
    exists left_refined, right_refined.
    repeat split; assumption.
Qed.

Theorem phase1_surface_dual_replay_fiber_membership_transport :
  forall left right left_refined right_refined
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related left right ->
    (phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         left_refined)
       (phase1_admitted_observation_key entry) <->
     phase1_surface_recursive_grouping_observation_related
       (phase1_surface_recursive_grouping_implementation_declaration_spine
         right_refined)
       (phase1_admitted_observation_key entry)).
Proof.
  intros left right left_refined right_refined entry Hleft Hright Hrelated.
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    left left_refined Hleft).
  rewrite (phase1_surface_observation_admitted_replay_exact_key
    right right_refined Hright).
  split; intro Hmember.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + apply phase1_surface_recursive_grouping_observation_related_symmetric.
      exact Hrelated.
    + exact Hmember.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + exact Hrelated.
    + exact Hmember.
Qed.

Theorem phase1_surface_dual_replay_shared_certificate_forces_related :
  forall left right left_refined right_refined
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_admitted_observation_key entry) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined)
      (phase1_admitted_observation_key entry) ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined).
Proof.
  intros left right left_refined right_refined entry
    Hleft Hright Hleft_member Hright_member.
  apply (proj2 (phase1_surface_dual_replay_related_iff_observations
    left right left_refined right_refined Hleft Hright)).
  eapply (phase1_surface_shared_certificate_forces_equal_observations
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      left_refined)
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      right_refined)
    (phase1_surface_observe_recursive_grouping_record_data left_refined)
    (phase1_surface_observe_recursive_grouping_record_data right_refined)
    entry).
  - exact (phase1_surface_observation_admitted_replay_value
      left left_refined Hleft).
  - exact (phase1_surface_observation_admitted_replay_value
      right right_refined Hright).
  - exact Hleft_member.
  - exact Hright_member.
Qed.

Theorem phase1_surface_dual_replay_distinct_certificates_separated :
  forall left right left_refined right_refined
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_admitted_observation first <>
      phase1_surface_admitted_observation second ->
    ~ (phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           left_refined)
         (phase1_admitted_observation_key first) /\
       phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           right_refined)
         (phase1_admitted_observation_key second) /\
       phase1_surface_recursive_grouping_observation_related
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           left_refined)
         (phase1_surface_recursive_grouping_implementation_declaration_spine
           right_refined)).
Proof.
  intros left right left_refined right_refined first second
    Hleft Hright Hdistinct [Hfirst [Hsecond Hrelated]].
  apply (phase1_surface_distinct_certificates_cannot_share_successful_fiber
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      left_refined)
    (phase1_surface_observe_recursive_grouping_record_data left_refined)
    first second
    (phase1_surface_observation_admitted_replay_value
      left left_refined Hleft)
    Hdistinct).
  split.
  - exact Hfirst.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + exact Hrelated.
    + exact Hsecond.
Qed.

Theorem phase1_surface_dual_replay_related_preserves_tag :
  forall left right left_refined right_refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      left = Some left_refined ->
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      right = Some right_refined ->
    phase1_surface_recursive_grouping_observation_related
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        left_refined)
      (phase1_surface_recursive_grouping_implementation_declaration_spine
        right_refined) ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right left_refined right_refined Hleft Hright Hrelated.
  apply phase1_surface_recursive_grouping_observation_related_preserves_tag.
  apply (proj1 (phase1_surface_dual_replay_related_iff_original
    left right left_refined right_refined Hleft Hright)).
  exact Hrelated.
Qed.

Example phase1_surface_dual_replay_rejected_record_excluded :
  forall refined,
    ~ phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
        (phase1_surface_recursive_grouping_implementation_declaration_spine
          refined).
Proof.
  intros refined.
  apply phase1_surface_recursive_grouping_rejected_key_unrelated.
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
