From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstRecordDataRecursiveGroupingObservationClassifier
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathDecision
  GrammarAstRecordDataRecursiveGroupingObservationReplayPathBooleanPER.

Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: extensional boolean replay-path
  fibers. A successful admitted edge preserves every neighbor test,
  and equality of neighbor rows characterizes the same admitted fiber
  ONLY when a successful endpoint supplies support. Rejected public
  carriers have identical empty rows but never connect to each other.

  Proof-side only; no parser, grammar, normalization, production
  Haskell AST, trusted admission or TCB change; no exact public-key
  injectivity, G2/G4 proof, or Phase 1 closure.
*)

Theorem phase1_surface_replay_connectedb_row_invariant :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true ->
    forall probe,
      phase1_surface_replay_path_connectedb left probe =
      phase1_surface_replay_path_connectedb right probe.
Proof.
  intros left right Hlink probe.
  assert (Hreverse :
    phase1_surface_replay_path_connectedb right left = true).
  {
    rewrite <- (phase1_surface_replay_connectedb_symmetric left right).
    exact Hlink.
  }
  destruct (phase1_surface_replay_path_connectedb left probe) eqn:Hleft;
    destruct (phase1_surface_replay_path_connectedb right probe) eqn:Hright;
    try reflexivity.
  - exfalso.
    pose proof (phase1_surface_replay_connectedb_transitive
      right left probe Hreverse Hleft) as Hbad.
    rewrite Hright in Hbad.
    discriminate Hbad.
  - exfalso.
    pose proof (phase1_surface_replay_connectedb_transitive
      left right probe Hlink Hright) as Hbad.
    rewrite Hleft in Hbad.
    discriminate Hbad.
Qed.

Theorem phase1_surface_replay_connectedb_column_invariant :
  forall left right,
    phase1_surface_replay_path_connectedb left right = true ->
    forall probe,
      phase1_surface_replay_path_connectedb probe left =
      phase1_surface_replay_path_connectedb probe right.
Proof.
  intros left right Hlink probe.
  rewrite (phase1_surface_replay_connectedb_symmetric probe left).
  rewrite (phase1_surface_replay_connectedb_symmetric probe right).
  exact (phase1_surface_replay_connectedb_row_invariant left right Hlink probe).
Qed.

Theorem phase1_surface_replay_connectedb_supported_row_characterization :
  forall left right,
    phase1_surface_replay_path_connectedb left left = true ->
    (phase1_surface_replay_path_connectedb left right = true <->
     forall probe,
       phase1_surface_replay_path_connectedb left probe =
       phase1_surface_replay_path_connectedb right probe).
Proof.
  intros left right Hsupport.
  split.
  - apply phase1_surface_replay_connectedb_row_invariant.
  - intro Hrows.
    specialize (Hrows left).
    rewrite Hsupport in Hrows.
    rewrite (phase1_surface_replay_connectedb_symmetric left right).
    symmetry.
    exact Hrows.
Qed.

Theorem phase1_surface_replay_connectedb_supported_column_characterization :
  forall left right,
    phase1_surface_replay_path_connectedb left left = true ->
    (phase1_surface_replay_path_connectedb left right = true <->
     forall probe,
       phase1_surface_replay_path_connectedb probe left =
       phase1_surface_replay_path_connectedb probe right).
Proof.
  intros left right Hsupport.
  split.
  - apply phase1_surface_replay_connectedb_column_invariant.
  - intro Hcolumns.
    apply (proj2 (phase1_surface_replay_connectedb_supported_row_characterization
      left right Hsupport)).
    intro probe.
    specialize (Hcolumns probe).
    rewrite <- (phase1_surface_replay_connectedb_symmetric probe left).
    rewrite <- (phase1_surface_replay_connectedb_symmetric probe right).
    exact Hcolumns.
Qed.

Theorem phase1_surface_replay_connectedb_rejected_row_empty :
  forall left,
    phase1_surface_normalized_observation left = None ->
    forall probe,
      phase1_surface_replay_path_connectedb left probe = false.
Proof.
  intros left Hreject probe.
  apply phase1_surface_replay_path_connectedb_rejected_left.
  exact Hreject.
Qed.

Theorem phase1_surface_replay_connectedb_rejected_column_empty :
  forall right,
    phase1_surface_normalized_observation right = None ->
    forall probe,
      phase1_surface_replay_path_connectedb probe right = false.
Proof.
  intros right Hreject probe.
  apply phase1_surface_replay_path_connectedb_rejected_right.
  exact Hreject.
Qed.

Theorem phase1_surface_replay_connectedb_rejected_rows_indistinguishable :
  forall left right,
    phase1_surface_normalized_observation left = None ->
    phase1_surface_normalized_observation right = None ->
    (forall probe,
      phase1_surface_replay_path_connectedb left probe =
      phase1_surface_replay_path_connectedb right probe) /\
    phase1_surface_replay_path_connectedb left right = false.
Proof.
  intros left right Hleft Hright.
  split.
  - intro probe.
    rewrite (phase1_surface_replay_connectedb_rejected_row_empty
      left Hleft probe).
    rewrite (phase1_surface_replay_connectedb_rejected_row_empty
      right Hright probe).
    reflexivity.
  - apply phase1_surface_replay_connectedb_rejected_row_empty.
    exact Hleft.
Qed.

Theorem phase1_surface_replay_connectedb_supported_rejected_rows_separated :
  forall left right,
    phase1_surface_replay_path_connectedb left left = true ->
    phase1_surface_normalized_observation right = None ->
    exists probe,
      phase1_surface_replay_path_connectedb left probe = true /\
      phase1_surface_replay_path_connectedb right probe = false.
Proof.
  intros left right Hsupport Hreject.
  exists left.
  split.
  - exact Hsupport.
  - apply phase1_surface_replay_connectedb_rejected_row_empty.
    exact Hreject.
Qed.

Theorem phase1_surface_replay_connectedb_nonempty_row_iff_support :
  forall left,
    (exists probe, phase1_surface_replay_path_connectedb left probe = true) <->
    phase1_surface_replay_path_connectedb left left = true.
Proof.
  intro left.
  split.
  - intros [probe Hconnected].
    destruct (phase1_surface_replay_connectedb_endpoints_supported
      left probe Hconnected) as [Hself _].
    exact Hself.
  - intro Hsupport.
    exists left.
    exact Hsupport.
Qed.

Example phase1_surface_replay_connectedb_malformed_record_row_empty :
  forall probe,
    phase1_surface_replay_path_connectedb
      {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
         phase1_declaration_spine_selected_tree := PTLiteral "Nat" |}
      probe = false.
Proof.
  intro probe.
  apply phase1_surface_replay_path_connectedb_malformed_record_rejected.
Qed.
