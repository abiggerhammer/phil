From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationClassifierCertificates
  GrammarAstRecordDataRecursiveGroupingObservationDerivedPairFibers
  GrammarAstRecordDataRecursiveGroupingObservationDerivedFiberCertificates.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: coherence of successful admission
  certificates with the fail-closed option-valued Record/Data classifier.
  A public key cannot acquire conflicting observed values from distinct
  certificates. Membership of a successful observation fiber agrees
  with the observation of EVERY valid certificate for its member.
  Canonical Record and Data derivations yield pinned certificate fibers,
  and their certificate-observation families remain disjoint.

  Proof-side only: no exact-key injectivity, grammar or TCB change,
  new admission, production AST binding, G2/G4, or Phase 1 closure.
*)

Theorem phase1_surface_same_key_certificates_agree :
  forall (first second : Phase1SurfaceAdmittedObservationKey),
    phase1_admitted_observation_key first =
      phase1_admitted_observation_key second ->
    phase1_surface_admitted_observation first =
      phase1_surface_admitted_observation second.
Proof.
  intros first second Hkey.
  pose proof (phase1_surface_classifier_matches_admitted_certificate first)
    as Hfirst.
  pose proof (phase1_surface_classifier_matches_admitted_certificate second)
    as Hsecond.
  rewrite Hkey in Hfirst.
  rewrite Hfirst in Hsecond.
  injection Hsecond as Hobs.
  exact Hobs.
Qed.

Theorem phase1_surface_certificate_fiber_membership_iff_observation :
  forall center observed (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center = Some observed ->
    (phase1_surface_recursive_grouping_observation_related
       center (phase1_admitted_observation_key entry) <->
     phase1_surface_admitted_observation entry = observed).
Proof.
  intros center observed entry Hcenter.
  split.
  - intro Hrelated.
    pose proof
      (proj2 (phase1_surface_observation_fiber_iff_related
        center (phase1_admitted_observation_key entry) observed Hcenter)
        Hrelated) as Hmember.
    rewrite (phase1_surface_classifier_matches_admitted_certificate entry)
      in Hmember.
    injection Hmember as Hobs.
    exact Hobs.
  - intro Hobs.
    apply (proj1 (phase1_surface_observation_fiber_iff_related
      center (phase1_admitted_observation_key entry) observed Hcenter)).
    rewrite (phase1_surface_classifier_matches_admitted_certificate entry).
    now rewrite Hobs.
Qed.

Theorem phase1_surface_derived_record_fiber_all_certificates_coherent :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed /\
      forall entry : Phase1SurfaceAdmittedObservationKey,
        (phase1_surface_recursive_grouping_observation_related
          {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
             phase1_declaration_spine_selected_tree := tree |}
          (phase1_admitted_observation_key entry) <->
         phase1_surface_admitted_observation entry = observed).
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_record_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  exists observed.
  split; [exact Hcenter |].
  intro entry.
  apply (phase1_surface_certificate_fiber_membership_iff_observation
    _ observed entry Hcenter).
Qed.

Theorem phase1_surface_derived_data_fiber_all_certificates_coherent :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed /\
      forall entry : Phase1SurfaceAdmittedObservationKey,
        (phase1_surface_recursive_grouping_observation_related
          {| phase1_declaration_spine_tag := Phase1DataDeclaration;
             phase1_declaration_spine_selected_tree := tree |}
          (phase1_admitted_observation_key entry) <->
         phase1_surface_admitted_observation entry = observed).
Proof.
  intros path input rest tree Hderive.
  destruct (phase1_surface_derived_data_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  exists observed.
  split; [exact Hcenter |].
  intro entry.
  apply (phase1_surface_certificate_fiber_membership_iff_observation
    _ observed entry Hcenter).
Qed.

Theorem phase1_surface_derived_record_data_member_certificates_distinct :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree
         (record_entry data_entry : Phase1SurfaceAdmittedObservationKey),
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := record_tree |}
      (phase1_admitted_observation_key record_entry) ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := data_tree |}
      (phase1_admitted_observation_key data_entry) ->
    phase1_surface_admitted_observation record_entry <>
      phase1_surface_admitted_observation data_entry.
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree
    record_entry data_entry Hrecord Hdata Hrecord_member Hdata_member.
  destruct (phase1_surface_derived_record_data_fibers_disjoint
    record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree Hrecord Hdata)
    as [record_observed [data_observed
      [Hrecord_center [Hdata_center Hdistinct]]]].
  pose proof (proj1
    (phase1_surface_certificate_fiber_membership_iff_observation
      _ record_observed record_entry Hrecord_center)
      Hrecord_member) as Hrecord_observed.
  pose proof (proj1
    (phase1_surface_certificate_fiber_membership_iff_observation
      _ data_observed data_entry Hdata_center)
      Hdata_member) as Hdata_observed.
  rewrite Hrecord_observed, Hdata_observed.
  exact Hdistinct.
Qed.

Example phase1_surface_mismatched_certificate_cannot_join_fiber :
  forall center observed (entry : Phase1SurfaceAdmittedObservationKey),
    phase1_surface_normalized_observation center = Some observed ->
    phase1_surface_admitted_observation entry <> observed ->
    ~ phase1_surface_recursive_grouping_observation_related
        center (phase1_admitted_observation_key entry).
Proof.
  intros center observed entry Hcenter Hmismatch Hrelated.
  apply Hmismatch.
  apply (proj1 (phase1_surface_certificate_fiber_membership_iff_observation
    center observed entry Hcenter)).
  exact Hrelated.
Qed.
