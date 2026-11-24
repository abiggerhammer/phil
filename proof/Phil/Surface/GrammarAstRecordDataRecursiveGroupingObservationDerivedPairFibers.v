From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationClassifierCertificates.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: classify nonvacuous observational
  fibers using the fail-closed option-valued Record/Data classifier.
  A successful fiber is exactly a relatedness class, and two canonical
  Grammar-v1 derivations can be compared by their admitted observations.
  Distinct Record/Data families cannot share a successful fiber.

  Proof-side only. No new parser admission, exact-key injectivity,
  Grammar-v1/TCB change, production AST binding, G2/G4 result,
  or Phase 1 closure.
*)

Theorem phase1_surface_observation_fiber_iff_related :
  forall center other observed,
    phase1_surface_normalized_observation center = Some observed ->
    (phase1_surface_normalized_observation other = Some observed <->
     phase1_surface_recursive_grouping_observation_related center other).
Proof.
  intros center other observed Hcenter.
  split.
  - intro Hother.
    apply (proj1 (phase1_surface_classifier_nonempty_equality_iff_related
      center other)).
    split.
    + now rewrite Hcenter, Hother.
    + rewrite Hcenter.
      discriminate.
  - intro Hrelated.
    pose proof (proj2 (phase1_surface_classifier_nonempty_equality_iff_related
      center other) Hrelated) as [Heq _].
    rewrite Hcenter in Heq.
    symmetry.
    exact Heq.
Qed.

Theorem phase1_surface_derived_record_pair_fiber_characterization :
  forall left_path left_input left_rest left_tree
         right_path right_input right_rest right_tree,
    Derives phase1_surface_rules left_path (ENonterminal "record_decl")
      left_input left_rest left_tree ->
    Derives phase1_surface_rules right_path (ENonterminal "record_decl")
      right_input right_rest right_tree ->
    exists left_observed right_observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |} = Some left_observed /\
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} = Some right_observed /\
      (phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} <-> left_observed = right_observed).
Proof.
  intros left_path left_input left_rest left_tree
    right_path right_input right_rest right_tree Hleft_derive Hright_derive.
  destruct (phase1_surface_derived_record_classifier_success
    left_path left_input left_rest left_tree Hleft_derive)
    as [left_observed Hleft].
  destruct (phase1_surface_derived_record_classifier_success
    right_path right_input right_rest right_tree Hright_derive)
    as [right_observed Hright].
  exists left_observed, right_observed.
  split; [exact Hleft |].
  split; [exact Hright |].
  split.
  - intro Hrelated.
    pose proof (proj2 (phase1_surface_classifier_nonempty_equality_iff_related
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |}) Hrelated) as [Heq _].
    rewrite Hleft, Hright in Heq.
    injection Heq as Hobserved.
    exact Hobserved.
  - intro Hobserved.
    apply (proj1 (phase1_surface_classifier_nonempty_equality_iff_related
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |})).
    split.
    + rewrite Hleft, Hright.
      now rewrite Hobserved.
    + rewrite Hleft.
      discriminate.
Qed.


Theorem phase1_surface_derived_data_pair_fiber_characterization :
  forall left_path left_input left_rest left_tree
         right_path right_input right_rest right_tree,
    Derives phase1_surface_rules left_path (ENonterminal "data_decl")
      left_input left_rest left_tree ->
    Derives phase1_surface_rules right_path (ENonterminal "data_decl")
      right_input right_rest right_tree ->
    exists left_observed right_observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |} = Some left_observed /\
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} = Some right_observed /\
      (phase1_surface_recursive_grouping_observation_related
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |} <-> left_observed = right_observed).
Proof.
  intros left_path left_input left_rest left_tree
    right_path right_input right_rest right_tree Hleft_derive Hright_derive.
  destruct (phase1_surface_derived_data_classifier_success
    left_path left_input left_rest left_tree Hleft_derive)
    as [left_observed Hleft].
  destruct (phase1_surface_derived_data_classifier_success
    right_path right_input right_rest right_tree Hright_derive)
    as [right_observed Hright].
  exists left_observed, right_observed.
  split; [exact Hleft |].
  split; [exact Hright |].
  split.
  - intro Hrelated.
    pose proof (proj2 (phase1_surface_classifier_nonempty_equality_iff_related
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |}) Hrelated) as [Heq _].
    rewrite Hleft, Hright in Heq.
    injection Heq as Hobserved.
    exact Hobserved.
  - intro Hobserved.
    apply (proj1 (phase1_surface_classifier_nonempty_equality_iff_related
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := left_tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := right_tree |})).
    split.
    + rewrite Hleft, Hright.
      now rewrite Hobserved.
    + rewrite Hleft.
      discriminate.
Qed.

Theorem phase1_surface_derived_record_data_fibers_disjoint :
  forall record_path record_input record_rest record_tree
         data_path data_input data_rest data_tree,
    Derives phase1_surface_rules record_path (ENonterminal "record_decl")
      record_input record_rest record_tree ->
    Derives phase1_surface_rules data_path (ENonterminal "data_decl")
      data_input data_rest data_tree ->
    exists record_observed data_observed,
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |} = Some record_observed /\
      phase1_surface_normalized_observation
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |} = Some data_observed /\
      record_observed <> data_observed.
Proof.
  intros record_path record_input record_rest record_tree
    data_path data_input data_rest data_tree Hrecord_derive Hdata_derive.
  destruct (phase1_surface_derived_record_classifier_success
    record_path record_input record_rest record_tree Hrecord_derive)
    as [record_observed Hrecord].
  destruct (phase1_surface_derived_data_classifier_success
    data_path data_input data_rest data_tree Hdata_derive)
    as [data_observed Hdata].
  exists record_observed, data_observed.
  split; [exact Hrecord |].
  split; [exact Hdata |].
  intro Heq.
  apply (phase1_surface_record_data_normalized_observation_separated
    record_tree data_tree).
  exists record_observed.
  split; [exact Hrecord |].
  rewrite <- Heq in Hdata.
  exact Hdata.
Qed.
