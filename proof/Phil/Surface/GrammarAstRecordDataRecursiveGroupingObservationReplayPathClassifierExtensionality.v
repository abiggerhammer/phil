From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanPER
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanRows
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierFibers.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: total extensionality of replay-path
  boolean neighbor rows and columns. Equality of all adjacency tests
  is equality of option-valued classifiers, including rejected
  None/None collisions; those collisions are NOT admitted replay edges.
  Proof-only; no Grammar-v1, normalizer, implementation, TCB,
  production AST binding, G2/G4, or Phase 1 closure changes.
*)

Theorem phase1_surface_replay_rows_equal_iff_classifier_equal :
  forall left right,
    ((forall probe,
       phase1_surface_replay_path_connectedb left probe =
       phase1_surface_replay_path_connectedb right probe) <->
     phase1_surface_normalized_observation left =
     phase1_surface_normalized_observation right).
Proof.
  intros left right.
  destruct (phase1_surface_normalized_observation left)
    as [left_observed|] eqn:Hleft;
  destruct (phase1_surface_normalized_observation right)
    as [right_observed|] eqn:Hright.
  - split.
    + intro Hrows.
      pose proof (proj1
        (phase1_surface_replay_fiber_successful_rows_iff_observations
          left right left_observed right_observed Hleft Hright)
        Hrows) as Hsame.
      now rewrite Hsame.
    + intro Hequal.
      injection Hequal as Hsame.
      apply (proj2
        (phase1_surface_replay_fiber_successful_rows_iff_observations
          left right left_observed right_observed Hleft Hright)).
      exact Hsame.
  - split.
    + intro Hrows.
      assert (Hsupport :
        phase1_surface_replay_path_connectedb left left = true).
      {
        apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success left)).
        now exists left_observed.
      }
      specialize (Hrows left).
      rewrite Hsupport in Hrows.
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        right Hright left) in Hrows.
      discriminate Hrows.
    + intro Hequal.
      discriminate Hequal.
  - split.
    + intro Hrows.
      assert (Hsupport :
        phase1_surface_replay_path_connectedb right right = true).
      {
        apply (proj2 (phase1_surface_replay_connectedb_diagonal_iff_success right)).
        now exists right_observed.
      }
      specialize (Hrows right).
      rewrite Hsupport in Hrows.
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        left Hleft right) in Hrows.
      discriminate Hrows.
    + intro Hequal.
      discriminate Hequal.
  - split.
    + intro Hrows.
      reflexivity.
    + intro Hequal.
      intro probe.
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        left Hleft probe).
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        right Hright probe).
      reflexivity.
Qed.

Theorem phase1_surface_replay_columns_equal_iff_classifier_equal :
  forall left right,
    ((forall probe,
       phase1_surface_replay_path_connectedb probe left =
       phase1_surface_replay_path_connectedb probe right) <->
     phase1_surface_normalized_observation left =
     phase1_surface_normalized_observation right).
Proof.
  intros left right.
  split.
  - intro Hcolumns.
    apply (proj1 (phase1_surface_replay_rows_equal_iff_classifier_equal
      left right)).
    intro probe.
    rewrite (phase1_surface_replay_connectedb_symmetric left probe).
    rewrite (phase1_surface_replay_connectedb_symmetric right probe).
    exact (Hcolumns probe).
  - intro Hequal.
    pose proof (proj2
      (phase1_surface_replay_rows_equal_iff_classifier_equal left right)
      Hequal) as Hrows.
    intro probe.
    rewrite (phase1_surface_replay_connectedb_symmetric probe left).
    rewrite (phase1_surface_replay_connectedb_symmetric probe right).
    exact (Hrows probe).
Qed.

Theorem phase1_surface_replay_equal_disconnected_rows_iff_rejected :
  forall left right,
    (((forall probe,
       phase1_surface_replay_path_connectedb left probe =
       phase1_surface_replay_path_connectedb right probe) /\
      phase1_surface_replay_path_connectedb left right = false) <->
     phase1_surface_normalized_observation left = None /\
     phase1_surface_normalized_observation right = None).
Proof.
  intros left right.
  split.
  - intros [Hrows Hdisconnected].
    pose proof (proj1
      (phase1_surface_replay_rows_equal_iff_classifier_equal left right)
      Hrows) as Hequal.
    destruct (phase1_surface_normalized_observation left)
      as [observed|] eqn:Hleft.
    + assert (Hright :
        phase1_surface_normalized_observation right = Some observed).
      { rewrite <- Hequal. exact Hleft. }
      pose proof (phase1_surface_replay_fiber_equal_observations_connected
        left right observed Hleft Hright) as Hconnected.
      rewrite Hdisconnected in Hconnected.
      discriminate Hconnected.
    + split.
      * exact Hleft.
      * rewrite <- Hequal. exact Hleft.
  - intros [Hleft Hright].
    split.
    + intro probe.
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        left Hleft probe).
      rewrite (phase1_surface_replay_connectedb_rejected_row_empty
        right Hright probe).
      reflexivity.
    + apply phase1_surface_replay_path_connectedb_rejected_left.
      exact Hleft.
Qed.

Example phase1_surface_replay_malformed_record_row_collides_with_rejected :
  forall rejected,
    phase1_surface_normalized_observation rejected = None ->
    (forall probe,
      phase1_surface_replay_path_connectedb
        {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
           phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
        probe =
      phase1_surface_replay_path_connectedb rejected probe) /\
    phase1_surface_replay_path_connectedb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      rejected = false.
Proof.
  intros rejected Hrejected.
  split.
  - intro probe.
    rewrite (phase1_surface_replay_connectedb_malformed_record_row_empty
      probe).
    rewrite (phase1_surface_replay_connectedb_rejected_row_empty
      rejected Hrejected probe).
    reflexivity.
  - apply phase1_surface_replay_path_connectedb_malformed_record_rejected.
Qed.
