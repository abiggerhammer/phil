From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanPER
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanRows.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: anchor the boolean replay-path
  adjacency rows and columns to concrete successful observations.
  A supported anchor's neighbors are exactly the declarations whose
  classifier returns the same Some observation. Successful classifiers
  have equal rows/columns exactly when their observations are equal,
  and distinct successful observations admit an explicit separating
  probe. Rejected carriers, including a malformed Record tag/tree,
  never become members of any supported fiber.

  Bounded proof-side correspondence only; no new runtime algorithm,
  parser/grammar, normalization, trusted admission, production AST
  binding, G2/G4 result, or Phase 1 closure. Public exact keys remain
  intentionally non-injective under observational equivalence.
*)

Theorem phase1_surface_replay_fiber_anchor_row :
  forall anchor candidate observed,
    phase1_surface_normalized_observation anchor = Some observed ->
    (phase1_surface_replay_path_connectedb anchor candidate = true <->
     phase1_surface_normalized_observation candidate = Some observed).
Proof.
  intros anchor candidate observed Hanchor.
  split.
  - intro Hconnected.
    destruct (proj1 (phase1_surface_replay_path_connectedb_iff_same_success
      anchor candidate) Hconnected) as [seen [Hseen Hcandidate]].
    rewrite Hanchor in Hseen.
    inversion Hseen; subst seen.
    exact Hcandidate.
  - intro Hcandidate.
    apply (proj2 (phase1_surface_replay_path_connectedb_iff_same_success
      anchor candidate)).
    exists observed.
    split; assumption.
Qed.

Theorem phase1_surface_replay_fiber_anchor_column :
  forall anchor candidate observed,
    phase1_surface_normalized_observation anchor = Some observed ->
    (phase1_surface_replay_path_connectedb candidate anchor = true <->
     phase1_surface_normalized_observation candidate = Some observed).
Proof.
  intros anchor candidate observed Hanchor.
  rewrite (phase1_surface_replay_connectedb_symmetric candidate anchor).
  apply phase1_surface_replay_fiber_anchor_row.
  exact Hanchor.
Qed.

Theorem phase1_surface_replay_fiber_distinct_observations_disconnected :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    left_observed <> right_observed ->
    phase1_surface_replay_path_connectedb left right = false.
Proof.
  intros left right left_observed right_observed Hleft Hright Hneq.
  destruct (phase1_surface_replay_path_connectedb left right)
    eqn:Hconnected; [|reflexivity].
  apply (proj1 (phase1_surface_replay_fiber_anchor_row
    left right left_observed Hleft)) in Hconnected.
  rewrite Hright in Hconnected.
  apply Hneq.
  now injection Hconnected.
Qed.

Theorem phase1_surface_replay_fiber_equal_observations_connected :
  forall left right observed,
    phase1_surface_normalized_observation left = Some observed ->
    phase1_surface_normalized_observation right = Some observed ->
    phase1_surface_replay_path_connectedb left right = true.
Proof.
  intros left right observed Hleft Hright.
  apply (proj2 (phase1_surface_replay_fiber_anchor_row
    left right observed Hleft)).
  exact Hright.
Qed.

Theorem phase1_surface_replay_fiber_successful_rows_iff_observations :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    ((forall probe,
      phase1_surface_replay_path_connectedb left probe =
      phase1_surface_replay_path_connectedb right probe) <->
     left_observed = right_observed).
Proof.
  intros left right left_observed right_observed Hleft Hright.
  split.
  - intro Hrows.
    assert (Hself :
      phase1_surface_replay_path_connectedb left left = true).
    {
      apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
      now exists left_observed.
    }
    specialize (Hrows left).
    rewrite Hself in Hrows.
    symmetry in Hrows.
    apply (proj1 (phase1_surface_replay_fiber_anchor_row
      right left right_observed Hright)) in Hrows.
    rewrite Hleft in Hrows.
    now injection Hrows.
  - intro Hequal.
    subst right_observed.
    apply phase1_surface_replay_connectedb_row_invariant.
    apply (proj2 (phase1_surface_replay_fiber_anchor_row
      left right left_observed Hleft)).
    exact Hright.
Qed.

Theorem phase1_surface_replay_fiber_successful_columns_iff_observations :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    ((forall probe,
      phase1_surface_replay_path_connectedb probe left =
      phase1_surface_replay_path_connectedb probe right) <->
     left_observed = right_observed).
Proof.
  intros left right left_observed right_observed Hleft Hright.
  split.
  - intro Hcolumns.
    assert (Hself :
      phase1_surface_replay_path_connectedb left left = true).
    {
      apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
      now exists left_observed.
    }
    specialize (Hcolumns left).
    rewrite Hself in Hcolumns.
    symmetry in Hcolumns.
    apply (proj1 (phase1_surface_replay_fiber_anchor_row
      left right left_observed Hleft)) in Hcolumns.
    rewrite Hright in Hcolumns.
    now injection Hcolumns.
  - intro Hequal.
    subst right_observed.
    apply phase1_surface_replay_connectedb_column_invariant.
    apply (proj2 (phase1_surface_replay_fiber_anchor_row
      left right left_observed Hleft)).
    exact Hright.
Qed.

Theorem phase1_surface_replay_fiber_distinct_rows_have_probe :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    left_observed <> right_observed ->
    exists probe,
      phase1_surface_replay_path_connectedb left probe = true /\
      phase1_surface_replay_path_connectedb right probe = false.
Proof.
  intros left right left_observed right_observed Hleft Hright Hneq.
  exists left.
  split.
  - apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
    now exists left_observed.
  - rewrite (phase1_surface_replay_connectedb_symmetric right left).
    eapply phase1_surface_replay_fiber_distinct_observations_disconnected;
      eassumption.
Qed.

Theorem phase1_surface_replay_fiber_distinct_columns_have_probe :
  forall left right left_observed right_observed,
    phase1_surface_normalized_observation left = Some left_observed ->
    phase1_surface_normalized_observation right = Some right_observed ->
    left_observed <> right_observed ->
    exists probe,
      phase1_surface_replay_path_connectedb probe left = true /\
      phase1_surface_replay_path_connectedb probe right = false.
Proof.
  intros left right left_observed right_observed Hleft Hright Hneq.
  exists left.
  split.
  - apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
    now exists left_observed.
  - eapply phase1_surface_replay_fiber_distinct_observations_disconnected;
      eassumption.
Qed.

Theorem phase1_surface_replay_fiber_rejected_never_neighbor :
  forall anchor rejected observed,
    phase1_surface_normalized_observation anchor = Some observed ->
    phase1_surface_normalized_observation rejected = None ->
    phase1_surface_replay_path_connectedb anchor rejected = false.
Proof.
  intros anchor rejected observed Hanchor Hreject.
  destruct (phase1_surface_replay_path_connectedb anchor rejected)
    eqn:Hconnected; [|reflexivity].
  apply (proj1 (phase1_surface_replay_fiber_anchor_row
    anchor rejected observed Hanchor)) in Hconnected.
  rewrite Hreject in Hconnected.
  discriminate Hconnected.
Qed.

Example phase1_surface_replay_fiber_malformed_record_never_neighbor :
  forall anchor,
    phase1_surface_replay_path_connectedb anchor
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = false.
Proof.
  intro anchor.
  rewrite (phase1_surface_replay_connectedb_symmetric anchor
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}).
  apply phase1_surface_replay_path_connectedb_malformed_record_rejected.
Qed.
