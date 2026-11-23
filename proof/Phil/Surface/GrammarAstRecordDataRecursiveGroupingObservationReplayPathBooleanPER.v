From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingProductionObservables
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClosure
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathQuotient
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: boolean partial-equivalence laws
  for decidable finite admitted Record/Data replay-path connectivity.
  Symmetry and transitivity hold over the whole public carrier; boolean
  self-connectivity holds exactly on successfully observed carriers.
  A shared neighbor is a genuine admitted witness, never a pair of
  rejected endpoints classified as None.

  No Grammar-v1, normalization, TCB, or production binding change;
  no exact-key injectivity, G2/G4, or Phase 1 closure claim.
*)

Theorem phase1_surface_replay_connectedb_symmetric :
  forall left right,
    phase1_surface_replay_path_connectedb left right =
    phase1_surface_replay_path_connectedb right left.
Proof.
  intros left right.
  destruct (phase1_surface_replay_path_connectedb left right) eqn:Hlr;
    destruct (phase1_surface_replay_path_connectedb right left) eqn:Hrl;
    try reflexivity.
  - exfalso.
    pose proof (proj1
      (phase1_surface_replay_path_connectedb_iff left right) Hlr) as Hpath.
    pose proof (phase1_surface_replay_path_symmetric left right Hpath)
      as Hreverse.
    apply (proj2 (phase1_surface_replay_path_connectedb_iff right left))
      in Hreverse.
    rewrite Hrl in Hreverse.
    discriminate Hreverse.
  - exfalso.
    pose proof (proj1
      (phase1_surface_replay_path_connectedb_iff right left) Hrl) as Hpath.
    pose proof (phase1_surface_replay_path_symmetric right left Hpath)
      as Hreverse.
    apply (proj2 (phase1_surface_replay_path_connectedb_iff left right))
      in Hreverse.
    rewrite Hlr in Hreverse.
    discriminate Hreverse.
Qed.

Theorem phase1_surface_replay_connectedb_transitive :
  forall left middle right,
    phase1_surface_replay_path_connectedb left middle = true ->
    phase1_surface_replay_path_connectedb middle right = true ->
    phase1_surface_replay_path_connectedb left right = true.
Proof.
  intros left middle right Hlm Hmr.
  apply (proj2 (phase1_surface_replay_path_connectedb_iff left right)).
  eapply phase1_surface_replay_path_transitive.
  - apply (proj1 (phase1_surface_replay_path_connectedb_iff left middle)).
    exact Hlm.
  - apply (proj1 (phase1_surface_replay_path_connectedb_iff middle right)).
    exact Hmr.
Qed.

Theorem phase1_surface_replay_connectedb_diagonal_iff_success :
  forall declaration,
    phase1_surface_replay_path_connectedb declaration declaration = true <->
    exists observed,
      phase1_surface_normalized_observation declaration = Some observed.
Proof.
  intro declaration.
  split.
  - intro Hconnected.
    apply (proj1 (phase1_surface_replay_path_connectedb_iff_same_success
      declaration declaration)) in Hconnected.
    destruct Hconnected as [observed [Hsome _]].
    now exists observed.
  - intros [observed Hsome].
    apply (proj2 (phase1_surface_replay_path_connectedb_iff_same_success
      declaration declaration)).
    exists observed.
    split; exact Hsome.
Qed.

Theorem phase1_surface_replay_connectedb_endpoints_supported :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true ->
    phase1_surface_replay_path_connectedb left left = true /\
    phase1_surface_replay_path_connectedb right right = true.
Proof.
  intros left right Hconnected.
  destruct (proj1 (phase1_surface_replay_path_connectedb_iff_same_success
    left right) Hconnected) as [observed [Hleft Hright]].
  split.
  - apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
    now exists observed.
  - apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success right)).
    now exists observed.
Qed.

Theorem phase1_surface_replay_connectedb_preserves_tag :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true ->
    phase1_declaration_spine_tag left = phase1_declaration_spine_tag right.
Proof.
  intros left right Hconnected.
  apply phase1_surface_replay_path_preserves_tag.
  apply (proj1 (phase1_surface_replay_path_connectedb_iff left right)).
  exact Hconnected.
Qed.

Theorem phase1_surface_replay_connectedb_record_data_separated :
  forall record_tree data_tree,
    phase1_surface_replay_path_connectedb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := record_tree |}
      {| phase1_declaration_spine_tag := Phase1DataDeclaration;
         phase1_declaration_spine_selected_tree := data_tree |} = false.
Proof.
  intros record_tree data_tree.
  destruct (phase1_surface_replay_path_connectedb
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := record_tree |}
    {| phase1_declaration_spine_tag := Phase1DataDeclaration;
       phase1_declaration_spine_selected_tree := data_tree |})
    eqn:Hconnected; [|reflexivity].
  exfalso.
  apply (phase1_surface_replay_path_record_data_separated
    record_tree data_tree).
  apply (proj1 (phase1_surface_replay_path_connectedb_iff _ _)).
  exact Hconnected.
Qed.

Theorem phase1_surface_replay_connectedb_common_neighbor :
  forall left middle right,
    phase1_surface_replay_path_connectedb left middle = true ->
    phase1_surface_replay_path_connectedb right middle = true ->
    phase1_surface_replay_path_connectedb left right = true.
Proof.
  intros left middle right Hleft Hright.
  eapply phase1_surface_replay_connectedb_transitive.
  - exact Hleft.
  - rewrite phase1_surface_replay_connectedb_symmetric.
    exact Hright.
Qed.

Theorem phase1_surface_replay_connectedb_iff_common_neighbor :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true <->
    exists middle,
      phase1_surface_replay_path_connectedb left middle = true /\
      phase1_surface_replay_path_connectedb right middle = true.
Proof.
  intros left right.
  split.
  - intro Hconnected.
    exists right.
    split.
    + exact Hconnected.
    + destruct (phase1_surface_replay_connectedb_endpoints_supported
        left right Hconnected) as [_ Hright].
      exact Hright.
  - intros [middle [Hleft Hright]].
    eapply phase1_surface_replay_connectedb_common_neighbor; eassumption.
Qed.

Example phase1_surface_replay_connectedb_two_rejections_not_neighbors :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_normalized_observation right = None ->
    phase1_surface_replay_path_connectedb left right = false.
Proof.
  intros left right Hleft _.
  apply phase1_surface_replay_path_connectedb_rejected_left.
  exact Hleft.
Qed.

Example phase1_surface_replay_connectedb_malformed_record_no_loop :
  phase1_surface_replay_path_connectedb
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = false.
Proof.
  apply phase1_surface_replay_path_connectedb_malformed_record_rejected.
Qed.
