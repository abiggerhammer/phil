From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingObservationPER
  GrammarAstRecordDataRecursiveGroupingObservationPERDomain
  GrammarAstRecordDataRecursiveGroupingObservationAdmittedQuotient
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClosure.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: the finite admitted replay-path
  relation is a partial equivalence relation with support exactly at
  successfully normalized public Record/Data keys. Reachability is
  equivalent to sharing an actual admitted certificate representative.
  Exact-key inequality can coexist with replay-path connectivity;
  Record and Data remain separated and rejected keys have no loops.

  This builds only on the already proved replay-path / observation-PER
  equivalence. No new normalization, axioms, Grammar-v1 / TCB changes,
  production Haskell AST binding, G2/G4 completion, or Phase 1 closure.
*)

Theorem phase1_surface_replay_path_reflexive_on_admission :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_admitted_replay_path declaration declaration.
Proof.
  intros declaration refined Hadmit.
  apply (proj2 (phase1_surface_replay_path_iff_related
    declaration declaration)).
  eapply phase1_surface_recursive_grouping_observation_related_reflexive_on_admission.
  exact Hadmit.
Qed.

Theorem phase1_surface_replay_path_support_iff_admission :
  forall declaration,
    phase1_surface_admitted_replay_path declaration declaration <->
    exists refined,
      phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
        declaration = Some refined.
Proof.
  intro declaration.
  split.
  - intro Hpath.
    apply (proj1 (phase1_surface_recursive_grouping_observation_support_iff_admission
      declaration)).
    apply phase1_surface_replay_path_related.
    exact Hpath.
  - intros [refined Hadmit].
    eapply phase1_surface_replay_path_reflexive_on_admission.
    exact Hadmit.
Qed.

Theorem phase1_surface_replay_path_symmetric :
  forall left right,
    phase1_surface_admitted_replay_path left right ->
    phase1_surface_admitted_replay_path right left.
Proof.
  intros left right Hpath.
  apply (proj2 (phase1_surface_replay_path_iff_related right left)).
  apply phase1_surface_recursive_grouping_observation_related_symmetric.
  apply phase1_surface_replay_path_related.
  exact Hpath.
Qed.

Theorem phase1_surface_replay_path_transitive :
  forall left middle right,
    phase1_surface_admitted_replay_path left middle ->
    phase1_surface_admitted_replay_path middle right ->
    phase1_surface_admitted_replay_path left right.
Proof.
  intros left middle right Hlm Hmr.
  exact (phase1_surface_admitted_replay_path_compose
    left middle right Hlm Hmr).
Qed.

Theorem phase1_surface_replay_path_iff_shared_certificate :
  forall left right,
    phase1_surface_admitted_replay_path left right <->
    exists entry : Phase1SurfaceAdmittedObservationKey,
      phase1_surface_recursive_grouping_observation_related
        left (phase1_admitted_observation_key entry) /\
      phase1_surface_recursive_grouping_observation_related
        right (phase1_admitted_observation_key entry).
Proof.
  intros left right.
  split.
  - intro Hpath.
    destruct (phase1_surface_replay_path_related left right Hpath)
      as [left_refined [right_refined [Hleft [Hright Hobserved]]]].
    exists
      {| phase1_admitted_observation_key := left;
         phase1_admitted_observation_refined := left_refined;
         phase1_admitted_observation_certificate := Hleft |}.
    split.
    + eapply phase1_surface_recursive_grouping_observation_related_reflexive_on_admission.
      exact Hleft.
    + apply phase1_surface_recursive_grouping_observation_related_symmetric.
      exists left_refined, right_refined.
      repeat split; assumption.
  - intros [entry [Hleft Hright]].
    apply (proj2 (phase1_surface_replay_path_iff_related left right)).
    eapply phase1_surface_recursive_grouping_observation_related_transitive.
    + exact Hleft.
    + apply phase1_surface_recursive_grouping_observation_related_symmetric.
      exact Hright.
Qed.

Theorem phase1_surface_replay_path_not_exact_key_equality :
  exists left right,
    phase1_surface_admitted_replay_path left right /\
    left <> right.
Proof.
  destruct phase1_surface_recursive_grouping_observation_related_not_exact_key_equality
    as [left [right [Hrelated Hdistinct]]].
  exists left, right.
  split.
  - apply (proj2 (phase1_surface_replay_path_iff_related left right)).
    exact Hrelated.
  - exact Hdistinct.
Qed.

Theorem phase1_surface_replay_path_record_data_separated :
  forall record_tree data_tree,
    ~ phase1_surface_admitted_replay_path
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := record_tree |}
        {| phase1_declaration_spine_tag := Phase1DataDeclaration;
           phase1_declaration_spine_selected_tree := data_tree |}.
Proof.
  intros record_tree data_tree Hpath.
  pose proof (phase1_surface_replay_path_preserves_tag
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := record_tree |}
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree := data_tree |}
    Hpath) as Htag.
  simpl in Htag.
  discriminate Htag.
Qed.

Example phase1_surface_replay_path_rejected_key_has_no_loop :
  forall declaration,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = None ->
    ~ phase1_surface_admitted_replay_path declaration declaration.
Proof.
  intros declaration Hreject Hpath.
  destruct (proj1 (phase1_surface_replay_path_support_iff_admission
    declaration) Hpath) as [refined Hadmit].
  rewrite Hreject in Hadmit.
  discriminate Hadmit.
Qed.
