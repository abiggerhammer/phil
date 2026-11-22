From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationCertificateFiberLaws
  GrammarAstRecordDataRecursiveGroupingObservationReplayPairCoherence.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: arbitrary finite nonempty paths
  of successfully normalized Record/Data public keys. Each primitive
  link carries both successful admissions and a relation between
  their reconstructed implementation views. Composition never
  introduces an unchecked intermediate carrier.

  Prove that path closure is exactly the existing observation PER,
  transports certificate membership, preserves declaration tags,
  excludes incompatible certificates, and rejects malformed public
  keys at either endpoint. No exact-key equality, Grammar-v1 or TCB
  change, production Haskell AST binding, G2/G4 or Phase 1 closure.
*)

Inductive phase1_surface_admitted_replay_path :
  Phase1SurfaceDeclarationSpine ->
  Phase1SurfaceDeclarationSpine -> Prop :=
| phase1_surface_admitted_replay_path_link :
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
      phase1_surface_admitted_replay_path left right
| phase1_surface_admitted_replay_path_compose :
    forall left middle right,
      phase1_surface_admitted_replay_path left middle ->
      phase1_surface_admitted_replay_path middle right ->
      phase1_surface_admitted_replay_path left right.

Theorem phase1_surface_replay_path_related :
  forall left right,
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_recursive_grouping_observation_related left right.
Proof.
  intros left right Hpath.
  induction Hpath as
    [left right left_refined right_refined Hleft Hright Hlink
    |left middle right Hlm IHlm Hmr IHmr].
  - apply (proj1 (phase1_surface_dual_replay_related_iff_original
      left right left_refined right_refined Hleft Hright)).
    exact Hlink.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive;
      eassumption.
Qed.

Theorem phase1_surface_replay_path_iff_related :
  forall left right,
    phase1_surface_admitted_replay_path left right <->
    phase1_surface_recursive_grouping_observation_related left right.
Proof.
  intros left right.
  split.
  - apply phase1_surface_replay_path_related.
  - intros [left_refined [right_refined [Hleft [Hright Hobserved]]]].
    apply (phase1_surface_admitted_replay_path_link
      left right left_refined right_refined Hleft Hright).
    apply (proj2 (phase1_surface_dual_replay_related_iff_original
      left right left_refined right_refined Hleft Hright)).
    exists left_refined, right_refined.
    repeat split; assumption.
Qed.

Theorem phase1_surface_replay_path_preserves_tag :
  forall left right,
    phase1_surface_admitted_replay_path left right ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right Hpath.
  apply phase1_surface_recursive_grouping_observation_related_preserves_tag.
  apply phase1_surface_replay_path_related.
  exact Hpath.
Qed.

Theorem phase1_surface_replay_path_certificate_fiber_transport :
  forall left right (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_admitted_replay_path left right ->
    (phase1_surface_recursive_grouping_observation_related
       left (phase1_admitted_observation_key entry) <->
     phase1_surface_recursive_grouping_observation_related
       right (phase1_admitted_observation_key entry)).
Proof.
  intros left right entry Hpath.
  pose proof (phase1_surface_replay_path_related left right Hpath)
    as Hrelated.
  split; intro Hmember.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + apply phase1_surface_recursive_grouping_observation_related_symmetric.
      exact Hrelated.
    + exact Hmember.
  - eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + exact Hrelated.
    + exact Hmember.
Qed.

Theorem phase1_surface_replay_path_distinct_certificates_separated :
  forall left right
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_admitted_observation first <>
      phase1_surface_admitted_observation second ->
    ~ (phase1_surface_recursive_grouping_observation_related
         left (phase1_admitted_observation_key first) /\
       phase1_surface_recursive_grouping_observation_related
         right (phase1_admitted_observation_key second)).
Proof.
  intros left right first second Hpath Hdistinct [Hfirst Hsecond].
  pose proof (phase1_surface_replay_path_related left right Hpath)
    as Hrelated.
  assert (Hright_first :
    phase1_surface_recursive_grouping_observation_related
      right (phase1_admitted_observation_key first)).
  {
    eapply phase1_surface_recursive_grouping_observation_related_transitive.
    - apply phase1_surface_recursive_grouping_observation_related_symmetric.
      exact Hrelated.
    - exact Hfirst.
  }
  destruct
    (phase1_surface_recursive_grouping_observation_related_has_admitted_endpoints
      right (phase1_admitted_observation_key second) Hsecond)
    as [[refined Hnormalize] _].
  apply (phase1_surface_distinct_certificates_cannot_share_successful_fiber
    right (phase1_surface_observe_recursive_grouping_record_data refined)
    first second Hnormalize Hdistinct).
  split; assumption.
Qed.

Example phase1_surface_replay_path_rejects_malformed_record_start :
  forall other,
    ~ phase1_surface_admitted_replay_path
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
        other.
Proof.
  intros other Hpath.
  apply (phase1_surface_recursive_grouping_rejected_key_unrelated
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
    other phase1_surface_impl_literal_under_record_tag_rejected).
  apply phase1_surface_replay_path_related.
  exact Hpath.
Qed.

Example phase1_surface_replay_path_rejects_malformed_record_end :
  forall other,
    ~ phase1_surface_admitted_replay_path
        other
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}.
Proof.
  intros other Hpath.
  apply (phase1_surface_recursive_grouping_rejected_key_unrelated
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
    other phase1_surface_impl_literal_under_record_tag_rejected).
  apply phase1_surface_recursive_grouping_observation_related_symmetric.
  apply phase1_surface_replay_path_related.
  exact Hpath.
Qed.
