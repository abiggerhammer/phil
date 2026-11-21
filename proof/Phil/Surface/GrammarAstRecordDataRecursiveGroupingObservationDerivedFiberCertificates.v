From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationClassifierCertificates
  GrammarAstRecordDataRecursiveGroupingObservationDerivedPairFibers
  GrammarAstRecordDataRecursiveGroupingObservationFiberPartition.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: make successful Record/Data
  observation-fiber membership constructive at the admission boundary.
  Every member of a successful fiber has its OWN successful admission
  certificate with the center's observation. Canonical Grammar-v1
  Record and Data derivations supply the center witness; rejected
  public intermediate carriers remain outside both families.

  This is a proof-only closure, not an exact-key identification, a
  new admission rule, production AST binding, Grammar-v1/TCB change,
  G2/G4 result, or Phase 1 closure.
*)

Theorem phase1_surface_successful_fiber_member_has_certificate :
  forall center member observed,
    phase1_surface_normalized_observation center = Some observed ->
    phase1_surface_recursive_grouping_observation_related center member ->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_admitted_observation_key entry = member /\
      phase1_surface_admitted_observation entry = observed.
Proof.
  intros center member observed Hcenter Hrelated.
  apply (proj1 (phase1_surface_classifier_some_iff_certified_observation
    member observed)).
  apply (proj2 (phase1_surface_observation_fiber_iff_related
    center member observed Hcenter)).
  exact Hrelated.
Qed.

Theorem phase1_surface_successful_fiber_member_iff_certificate :
  forall center member observed,
    phase1_surface_normalized_observation center = Some observed ->
    (phase1_surface_recursive_grouping_observation_related center member <->
     exists entry : Phase1SurfaceAdmittedObservationKey,
       phase1_admitted_observation_key entry = member /\
       phase1_surface_admitted_observation entry = observed).
Proof.
  intros center member observed Hcenter.
  split.
  - intro Hrelated.
    exact (phase1_surface_successful_fiber_member_has_certificate
      center member observed Hcenter Hrelated).
  - intro Hcertificate.
    apply (proj1 (phase1_surface_observation_fiber_iff_related
      center member observed Hcenter)).
    apply (proj2 (phase1_surface_classifier_some_iff_certified_observation
      member observed)).
    exact Hcertificate.
Qed.

Theorem phase1_surface_derived_record_fiber_member_has_certificate :
  forall path input rest tree member,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := tree |} member ->
    exists observed (entry : Phase1SurfaceAdmittedObservationKey),
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed /\
      phase1_admitted_observation_key entry = member /\
      phase1_surface_admitted_observation entry = observed.
Proof.
  intros path input rest tree member Hderive Hrelated.
  destruct (phase1_surface_derived_record_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  destruct (phase1_surface_successful_fiber_member_has_certificate
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := tree |}
    member observed Hcenter Hrelated) as [entry [Hkey Hobserved]].
  exists observed, entry.
  repeat split; assumption.
Qed.

Theorem phase1_surface_derived_data_fiber_member_has_certificate :
  forall path input rest tree member,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    phase1_surface_recursive_grouping_observation_related
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := tree |} member ->
    exists observed (entry : Phase1SurfaceAdmittedObservationKey),
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} = Some observed /\
      phase1_admitted_observation_key entry = member /\
      phase1_surface_admitted_observation entry = observed.
Proof.
  intros path input rest tree member Hderive Hrelated.
  destruct (phase1_surface_derived_data_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  destruct (phase1_surface_successful_fiber_member_has_certificate
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree := tree |}
    member observed Hcenter Hrelated) as [entry [Hkey Hobserved]].
  exists observed, entry.
  repeat split; assumption.
Qed.

Example phase1_surface_derived_record_fiber_rejects_unadmitted_member :
  forall path input rest tree member,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    phase1_surface_normalized_observation member = None ->
    ~ phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := tree |} member.
Proof.
  intros path input rest tree member Hderive Hreject Hrelated.
  destruct (phase1_surface_derived_record_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  exact (phase1_surface_rejected_observation_key_not_in_successful_fiber
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := tree |}
    member observed Hcenter Hreject Hrelated).
Qed.

Example phase1_surface_derived_data_fiber_rejects_unadmitted_member :
  forall path input rest tree member,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    phase1_surface_normalized_observation member = None ->
    ~ phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := tree |} member.
Proof.
  intros path input rest tree member Hderive Hreject Hrelated.
  destruct (phase1_surface_derived_data_classifier_success
    path input rest tree Hderive) as [observed Hcenter].
  exact (phase1_surface_rejected_observation_key_not_in_successful_fiber
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree := tree |}
    member observed Hcenter Hreject Hrelated).
Qed.
