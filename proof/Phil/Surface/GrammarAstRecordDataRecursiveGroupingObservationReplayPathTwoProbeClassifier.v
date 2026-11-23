From Stdlib Require Import Bool.Bool Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanPER
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanRows
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathClassifierExtensionality.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: finite endpoint-probe
  characterization of the already proved total classifier extensionality.
  Two endpoint probes suffice; equal rejected rows are not replay edges.
  No grammar, normalizer, production binding, TCB, G2/G4 or closure change.
*)

Theorem phase1_surface_replay_false_diagonal_row_empty :
  forall declaration,
    phase1_surface_replay_path_connectedb declaration declaration = false ->
    forall probe,
      phase1_surface_replay_path_connectedb declaration probe = false.
Proof.
  intros declaration Hdiagonal probe.
  destruct (phase1_surface_replay_path_connectedb declaration probe)
    eqn:Hprobe.
  - pose proof (proj1 (phase1_surface_replay_connectedb_endpoints_supported
      declaration probe Hprobe)) as Hsupport.
    rewrite Hdiagonal in Hsupport.
    discriminate Hsupport.
  - reflexivity.
Qed.

Theorem phase1_surface_replay_two_probes_iff_rows_equal :
  forall left right,
    ((phase1_surface_replay_path_connectedb left left =
      phase1_surface_replay_path_connectedb right left /\
      phase1_surface_replay_path_connectedb left right =
      phase1_surface_replay_path_connectedb right right) <->
     forall probe,
       phase1_surface_replay_path_connectedb left probe =
       phase1_surface_replay_path_connectedb right probe).
Proof.
  intros left right.
  split.
  - intros [Hleft Hright] probe.
    destruct (phase1_surface_replay_path_connectedb left left)
      eqn:Hleft_diagonal.
    + assert (Hedge :
        phase1_surface_replay_path_connectedb left right = true).
      {
        rewrite (phase1_surface_replay_connectedb_symmetric left right).
        congruence.
      }
      exact (phase1_surface_replay_connectedb_row_invariant
        left right Hedge probe).
    + destruct (phase1_surface_replay_path_connectedb right right)
        eqn:Hright_diagonal.
      * assert (Hedge :
          phase1_surface_replay_path_connectedb left right = true).
        { congruence. }
        exact (phase1_surface_replay_connectedb_row_invariant
          left right Hedge probe).
      * rewrite (phase1_surface_replay_false_diagonal_row_empty
          left Hleft_diagonal probe).
        rewrite (phase1_surface_replay_false_diagonal_row_empty
          right Hright_diagonal probe).
        reflexivity.
  - intro Hrows.
    split.
    + exact (Hrows left).
    + exact (Hrows right).
Qed.

Definition phase1_surface_replay_two_probe_equalb
  (left right : Phase1SurfaceDeclarationSpine) : bool :=
  andb
    (Bool.eqb (phase1_surface_replay_path_connectedb left left)
      (phase1_surface_replay_path_connectedb right left))
    (Bool.eqb (phase1_surface_replay_path_connectedb left right)
      (phase1_surface_replay_path_connectedb right right)).

Theorem phase1_surface_replay_two_probe_equalb_iff_rows :
  forall left right,
    phase1_surface_replay_two_probe_equalb left right = true <->
    forall probe,
      phase1_surface_replay_path_connectedb left probe =
      phase1_surface_replay_path_connectedb right probe.
Proof.
  intros left right.
  unfold phase1_surface_replay_two_probe_equalb.
  rewrite Bool.andb_true_iff.
  rewrite !Bool.eqb_true_iff.
  apply phase1_surface_replay_two_probes_iff_rows_equal.
Qed.

Theorem phase1_surface_replay_two_probe_equalb_iff_classifier :
  forall left right,
    phase1_surface_replay_two_probe_equalb left right = true <->
    phase1_surface_normalized_observation left =
    phase1_surface_normalized_observation right.
Proof.
  intros left right.
  rewrite phase1_surface_replay_two_probe_equalb_iff_rows.
  apply phase1_surface_replay_rows_equal_iff_classifier_equal.
Qed.

Example phase1_surface_replay_two_probe_malformed_rejected_collision :
  forall rejected,
    phase1_surface_normalized_observation rejected = None ->
    phase1_surface_replay_two_probe_equalb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      rejected = true /\
    phase1_surface_replay_path_connectedb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      rejected = false.
Proof.
  intros rejected Hrejected.
  pose proof (phase1_surface_replay_malformed_record_row_collides_with_rejected
    rejected Hrejected) as [Hrows Hdisconnected].
  split.
  - apply (proj2 (phase1_surface_replay_two_probe_equalb_iff_rows
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      rejected)).
    exact Hrows.
  - exact Hdisconnected.
Qed.
