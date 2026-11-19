From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

From Phil.Core Require Import Syntax DataProduct.

(*
  FSEM-01 DATA-04/05E: arbitrary finite binary product-tree *model*.
  No fixed nesting depth, and no new Axiom/Parameter/Admitted.

  The source AST => this tree, globally fresh declaration-rooted names,
  equality of concrete Haskell Ty/Text/Map/Set to model contracts and
  execution of the actual Surface/Core checker remain independent
  implementation/correspondence obligations, tested for finite source cases.
*)
Module D := DataProduct.

Inductive ProductTree : Type :=
| TreeLeaf (name : Syntax.Name)
| TreeFork
    (members : list D.ProductElementContract)
    (successors : list Syntax.Name)
    (leftTree rightTree : ProductTree).

Fixpoint treeStageCount (tree : ProductTree) : nat :=
  match tree with
  | TreeLeaf _ => 0
  | TreeFork _ _ leftTree rightTree =>
      S (treeStageCount leftTree + treeStageCount rightTree)
  end.

Fixpoint treeAccepted (tree : ProductTree) : Prop :=
  match tree with
  | TreeLeaf _ => True
  | TreeFork members successors leftTree rightTree =>
      D.ProductEliminationAccepted members successors /\
      treeAccepted leftTree /\ treeAccepted rightTree
  end.

(* One reached restoration, then the recursive leftTree and rightTree source
   subtrees in preorder; a failed stage has no fabricated successor. *)
Fixpoint replayProductTree (tree : ProductTree)
  : option (list (list D.RestoredProductBinding)) :=
  match tree with
  | TreeLeaf _ => Some []
  | TreeFork members successors leftTree rightTree =>
      match D.productRestorationPlan members successors with
      | None => None
      | Some restored =>
          match replayProductTree leftTree with
          | None => None
          | Some leftTrace =>
              match replayProductTree rightTree with
              | None => None
              | Some rightTrace =>
                  Some (restored :: leftTrace ++ rightTrace)
              end
          end
      end
  end.

Theorem data05e_accepted_finite_tree_replays :
  forall tree,
    treeAccepted tree ->
    exists trace, replayProductTree tree = Some trace.
Proof.
  induction tree as [leaf | members successors leftTree IHleft rightTree IHright].
  - intros _. exists []. reflexivity.
  - simpl. intros [Hroot [Hleft Hright]].
    destruct Hroot as [restored [Hplan _]].
    destruct (IHleft Hleft) as [leftTrace HleftTrace].
    destruct (IHright Hright) as [rightTrace HrightTrace].
    exists (restored :: leftTrace ++ rightTrace).
    now rewrite Hplan,HleftTrace,HrightTrace.
Qed.

Theorem data05e_failed_root_never_replays :
  forall members successors leftTree rightTree,
    D.productRestorationPlan members successors = None ->
    replayProductTree
      (TreeFork members successors leftTree rightTree) = None.
Proof.
  intros members successors leftTree rightTree H.
  simpl. now rewrite H.
Qed.

Theorem data05e_failed_left_subtree_never_replays :
  forall members successors leftTree rightTree,
    replayProductTree leftTree = None ->
    replayProductTree
      (TreeFork members successors leftTree rightTree) = None.
Proof.
  intros members successors leftTree rightTree H.
  simpl.
  destruct (D.productRestorationPlan members successors);
    [now rewrite H|reflexivity].
Qed.

Theorem data05e_failed_right_subtree_never_replays :
  forall members successors leftTree rightTree,
    replayProductTree rightTree = None ->
    replayProductTree
      (TreeFork members successors leftTree rightTree) = None.
Proof.
  intros members successors leftTree rightTree H.
  simpl.
  destruct (D.productRestorationPlan members successors);
    [|reflexivity].
  destruct (replayProductTree leftTree); [now rewrite H|reflexivity].
Qed.

(* Stage count follows the *tree*, rather than a hardcoded 2/3-level case. *)
Theorem data05e_successful_replay_has_exact_stage_count :
  forall tree trace,
    replayProductTree tree = Some trace ->
    List.length trace = treeStageCount tree.
Proof.
  induction tree as [leaf | members successors leftTree IHleft rightTree IHright];
    intros trace H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H.
    destruct (D.productRestorationPlan members successors) as [root|]
      eqn:Hroot; try discriminate.
    destruct (replayProductTree leftTree) as [leftTrace|] eqn:Hleft;
      try discriminate.
    destruct (replayProductTree rightTree) as [rightTrace|] eqn:Hright;
      try discriminate.
    inversion H; subst; clear H.
    simpl.
    rewrite length_app.
    rewrite (IHleft leftTrace eq_refl), (IHright rightTrace eq_refl).
    lia.
Qed.

(* The returned root restoration never fabricates a leaf, changes a mode
   or silently swaps the positional product type/name contract. *)
Theorem data05e_replayed_fork_preserves_exact_root_element :
  forall members successors leftTree rightTree trace
         index member owner,
    replayProductTree (TreeFork members successors leftTree rightTree) =
      Some trace ->
    nth_error members index = Some member ->
    nth_error successors index = Some owner ->
    exists first rest,
      trace = first :: rest /\
      nth_error first index =
        Some (D.mkRestoredProductBinding owner
          (D.productElementMode member) (D.productElementType member)).
Proof.
  intros members successors leftTree rightTree trace index member owner
    Hreplay Hmember Howner.
  simpl in Hreplay.
  destruct (D.productRestorationPlan members successors) as [first|]
    eqn:Hfirst; try discriminate.
  destruct (replayProductTree leftTree) as [leftTrace|]
    eqn:Hleft; try discriminate.
  destruct (replayProductTree rightTree) as [rightTrace|]
    eqn:Hright; try discriminate.
  inversion Hreplay; subst; clear Hreplay.
  exists first, (leftTrace ++ rightTrace).
  split; [reflexivity|].
  eapply D.restoration_plan_preserves_exact_element_contract; eauto.
Qed.

Print Assumptions data05e_accepted_finite_tree_replays.
Print Assumptions data05e_failed_root_never_replays.
Print Assumptions data05e_failed_left_subtree_never_replays.
Print Assumptions data05e_failed_right_subtree_never_replays.
Print Assumptions data05e_successful_replay_has_exact_stage_count.
Print Assumptions data05e_replayed_fork_preserves_exact_root_element.
