From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationCertificateCoherence.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: partition the successful
  Record/Data observation fibers by admitted certificate observations.
  A certificate cannot belong to two successful fibers with different
  observations. Equal observations give identical certificate-member
  predicates, even for distinct exact keys. Canonical Record and Data
  derivations cannot share any admitted certificate.

  Proof-only: no new admission or parsing, no exact-key injectivity,
  no Grammar-v1/TCB change, production AST binding, G2/G4 result,
  or Phase 1 closure.
*)

Theorem phase1_surface_shared_certificate_forces_equal_observations :
  forall center_left center_right left_observed right_observed
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center_left = Some left_observed ->
    phase1_surface_normalized_observation center_right = Some right_observed ->
    phase1_surface_recursive_grouping_observation_related
      center_left (phase1_admitted_observation_key entry) ->
    phase1_surface_recursive_grouping_observation_related
      center_right (phase1_admitted_observation_key entry) ->
    left_observed = right_observed.
Proof.
  intros center_left center_right left_observed right_observed
    entry Hleft Hright Hleft_member Hright_member.
  pose proof (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
    center_left left_observed entry Hleft) Hleft_member) as Hentry_left.
  pose proof (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
    center_right right_observed entry Hright) Hright_member) as Hentry_right.
  rewrite Hentry_left in Hentry_right.
  exact Hentry_right.
Qed.

Theorem phase1_surface_certificate_fibers_same_observation_same_members :
  forall center_left center_right observed
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center_left = Some observed ->
    phase1_surface_normalized_observation center_right = Some observed ->
    (phase1_surface_recursive_grouping_observation_related
       center_left (phase1_admitted_observation_key entry) <->
     phase1_surface_recursive_grouping_observation_related
       center_right (phase1_admitted_observation_key entry)).
Proof.
  intros center_left center_right observed entry Hleft Hright.
  split; intro Hmember.
  - apply (proj2 (phase1_surface_certificate_fiber_membership_iff_observation
      center_right observed entry Hright)).
    apply (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
      center_left observed entry Hleft)).
    exact Hmember.
  - apply (proj2 (phase1_surface_certificate_fiber_membership_iff_observation
      center_left observed entry Hleft)).
    apply (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
      center_right observed entry Hright)).
    exact Hmember.
Qed.

Theorem phase1_surface_equal_certificate_observations_same_fiber_membership :
  forall center observed
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center = Some observed ->
    phase1_surface_admitted_observation first =
      phase1_surface_admitted_observation second ->
    (phase1_surface_recursive_grouping_observation_related
       center (phase1_admitted_observation_key first) <->
     phase1_surface_recursive_grouping_observation_related
       center (phase1_admitted_observation_key second)).
Proof.
  intros center observed first second Hcenter Hequal.
  split; intro Hmember.
  - apply (proj2 (phase1_surface_certificate_fiber_membership_iff_observation
      center observed second Hcenter)).
    rewrite <- Hequal.
    apply (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
      center observed first Hcenter)).
    exact Hmember.
  - apply (proj2 (phase1_surface_certificate_fiber_membership_iff_observation
      center observed first Hcenter)).
    rewrite Hequal.
    apply (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
      center observed second Hcenter)).
    exact Hmember.
Qed.

Theorem phase1_surface_distinct_observation_fibers_have_no_common_certificate :
  forall center_left center_right left_observed right_observed
         (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center_left = Some left_observed ->
    phase1_surface_normalized_observation center_right = Some right_observed ->
    left_observed <> right_observed ->
    ~ (phase1_surface_recursive_grouping_observation_related
         center_left (phase1_admitted_observation_key entry) /\
       phase1_surface_recursive_grouping_observation_related
         center_right (phase1_admitted_observation_key entry)).
Proof.
  intros center_left center_right left_observed right_observed entry
    Hleft Hright Hdistinct [Hleft_member Hright_member].
  apply Hdistinct.
  exact (phase1_surface_shared_certificate_forces_equal_observations
    center_left center_right left_observed right_observed entry
    Hleft Hright Hleft_member Hright_member).
Qed.

Theorem phase1_surface_derived_record_data_have_no_common_certificate :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree
         (entry : Phase1SurfaceAdmittedObservationKey),
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    ~ (phase1_surface_recursive_grouping_observation_related
         {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
            phase1_declaration_spine_selected_tree := record_tree |}
         (phase1_admitted_observation_key entry) /\
       phase1_surface_recursive_grouping_observation_related
         {| phase1_declaration_spine_tag := Phase1DataDeclaration;
            phase1_declaration_spine_selected_tree := data_tree |}
         (phase1_admitted_observation_key entry)).
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree entry
    Hrecord Hdata [Hrecord_member Hdata_member].
  pose proof (phase1_surface_derived_record_data_member_certificates_distinct
    record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree entry entry
    Hrecord Hdata Hrecord_member Hdata_member) as Hdistinct.
  apply Hdistinct.
  reflexivity.
Qed.

Example phase1_surface_distinct_certificates_cannot_share_successful_fiber :
  forall center observed
         (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center = Some observed ->
    phase1_surface_admitted_observation first <>
      phase1_surface_admitted_observation second ->
    ~ (phase1_surface_recursive_grouping_observation_related
         center (phase1_admitted_observation_key first) /\
       phase1_surface_recursive_grouping_observation_related
         center (phase1_admitted_observation_key second)).
Proof.
  intros center observed first second Hcenter Hdistinct [Hfirst Hsecond].
  apply Hdistinct.
  pose proof (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
    center observed first Hcenter) Hfirst) as Hfirst_observation.
  pose proof (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
    center observed second Hcenter) Hsecond) as Hsecond_observation.
  now rewrite Hfirst_observation, Hsecond_observation.
Qed.
