From Stdlib Require Import Lists.List.
Import ListNotations.

From Phil.Core Require Import Syntax Context ContextJoin.

(*
  Proof-oriented model of Phil.Core.Process.joinBranches.

  The non-resource portion of CheckState is opaque.  The model preserves the
  flattened path list exactly and changes only the ResourceContext carried by a
  Continue path.  This isolates the semantic role of joinBranches from the
  representation of the rest of checker state.
*)

Parameter StatePayload : Type.

Record JoinState : Type := mkJoinState
  { joinResources : ResourceContext
  ; joinPayload : StatePayload
  }.

Record JoinPath : Type := mkJoinPath
  { joinControl : Control
  ; joinState : JoinState
  }.

Definition JoinProcessFlow := list JoinPath.
Definition BranchSet := list JoinProcessFlow.

Definition flattenBranches (flows : BranchSet) : list JoinPath := concat flows.

Fixpoint continuingContexts (paths : list JoinPath) : list ResourceContext :=
  match paths with
  | [] => []
  | path :: rest =>
      match joinControl path with
      | Continue => joinResources (joinState path) :: continuingContexts rest
      | Return _ => continuingContexts rest
      | Closed _ => continuingContexts rest
      | Failed _ _ => continuingContexts rest
      end
  end.

Definition normalizeContinue (joined : ResourceContext) (path : JoinPath) : JoinPath :=
  match joinControl path with
  | Continue =>
      mkJoinPath Continue
        (mkJoinState joined (joinPayload (joinState path)))
  | Return _ => path
  | Closed _ => path
  | Failed _ _ => path
  end.

Lemma normalize_noncontinuing_exact :
  forall joined path,
    joinControl path <> Continue ->
    normalizeContinue joined path = path.
Proof.
  intros joined path Hnoncontinuing.
  destruct path as [control state].
  simpl in Hnoncontinuing.
  destruct control; simpl.
  - exfalso. apply Hnoncontinuing. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma normalize_continuing_exact :
  forall joined path,
    joinControl path = Continue ->
    joinControl (normalizeContinue joined path) = Continue /\
    joinResources (joinState (normalizeContinue joined path)) = joined /\
    joinPayload (joinState (normalizeContinue joined path)) =
      joinPayload (joinState path).
Proof.
  intros joined path Hcontinue.
  destruct path as [control state].
  simpl in Hcontinue.
  destruct control; try discriminate.
  simpl. repeat split; reflexivity.
Qed.

Lemma continuing_contexts_contains :
  forall paths path,
    In path paths ->
    joinControl path = Continue ->
    In (joinResources (joinState path)) (continuingContexts paths).
Proof.
  induction paths as [| head tail IH]; intros path Hin Hcontinue.
  - inversion Hin.
  - simpl in Hin.
    destruct head as [control state].
    simpl.
    destruct Hin as [Heq | Hin].
    + subst path.
      simpl in Hcontinue.
      destruct control; try discriminate.
      simpl. left. reflexivity.
    + destruct control.
      * simpl. right. eapply IH; eauto.
      * simpl. eapply IH; eauto.
      * simpl. eapply IH; eauto.
      * simpl. eapply IH; eauto.
Qed.

Inductive ProcessJoinSuccess : BranchSet -> JoinProcessFlow -> Prop :=
| ProcessJoin_no_continuing :
    forall flows,
      flows <> [] ->
      continuingContexts (flattenBranches flows) = [] ->
      ProcessJoinSuccess flows (flattenBranches flows)
| ProcessJoin_continuing :
    forall flows first rest joined,
      flows <> [] ->
      continuingContexts (flattenBranches flows) = first :: rest ->
      ContextJoinSuccess (first :: rest) joined ->
      ProcessJoinSuccess
        flows
        (map (normalizeContinue joined) (flattenBranches flows)).

(* PHIL-PROC-JOIN-001: successful join requires at least one input branch. *)
Theorem process_join_nonempty_branch_set :
  forall flows output,
    ProcessJoinSuccess flows output ->
    flows <> [].
Proof.
  intros flows output Hjoin.
  destruct Hjoin; assumption.
Qed.

(* PHIL-PROC-JOIN-001: normalization never changes path multiplicity. *)
Theorem process_join_preserves_path_count :
  forall flows output,
    ProcessJoinSuccess flows output ->
    length output = length (flattenBranches flows).
Proof.
  intros flows output Hjoin.
  destruct Hjoin.
  - reflexivity.
  - apply map_length.
Qed.

(*
  PHIL-PROC-JOIN-001: Return, Closed, and Failed paths survive the join exactly.
  Since the output is a map over the flattened input, this also preserves their
  relative order and multiplicity.
*)
Theorem process_join_preserves_noncontinuing :
  forall flows output path,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path <> Continue ->
    In path output.
Proof.
  intros flows output path Hjoin Hin Hnoncontinuing.
  destruct Hjoin as
    [ flows Hnonempty Hnone
    | flows first rest joined Hnonempty Hcontexts HcontextJoin ].
  - exact Hin.
  - apply in_map_iff.
    exists path.
    split.
    + apply normalize_noncontinuing_exact. exact Hnoncontinuing.
    + exact Hin.
Qed.

(*
  PHIL-PROC-JOIN-001: every original Continue path is represented in the output
  with exactly the one joined ResourceContext and with its opaque checker-state
  payload unchanged.
*)
Theorem process_join_normalizes_every_continue :
  forall flows output path,
    ProcessJoinSuccess flows output ->
    In path (flattenBranches flows) ->
    joinControl path = Continue ->
    exists joined,
      ContextJoinSuccess (continuingContexts (flattenBranches flows)) joined /\
      In (normalizeContinue joined path) output /\
      joinControl (normalizeContinue joined path) = Continue /\
      joinResources (joinState (normalizeContinue joined path)) = joined /\
      joinPayload (joinState (normalizeContinue joined path)) =
        joinPayload (joinState path).
Proof.
  intros flows output path Hjoin Hin Hcontinue.
  destruct Hjoin as
    [ flows Hnonempty Hnone
    | flows first rest joined Hnonempty Hcontexts HcontextJoin ].
  - pose proof (continuing_contexts_contains _ _ Hin Hcontinue) as Hcontained.
    rewrite Hnone in Hcontained.
    contradiction.
  - exists joined.
    split.
    + rewrite Hcontexts. exact HcontextJoin.
    + split.
      * apply in_map. exact Hin.
      * pose proof (normalize_continuing_exact joined path Hcontinue) as Hnormalized.
        destruct Hnormalized as [Hcontrol [Hresources Hpayload]].
        repeat split; assumption.
Qed.
