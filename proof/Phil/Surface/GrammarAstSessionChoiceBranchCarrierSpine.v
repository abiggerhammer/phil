From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the now-closed session_branch shell through the select/offer branch
  list.  Branch labels, parameters, boundaries, guards, and continuations
  retain their current exact certified boundaries inside each branch carrier.
*)

Fixpoint phase1_surface_normalize_session_branch_spines
  (trees : list ParseTree) : option (list Phase1SurfaceSessionBranchSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_session_branch_spine tree,
            phase1_surface_normalize_session_branch_spines rest with
      | Some branch, Some branches => Some (branch :: branches)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_session_branch_spines_round_trip :
  forall trees branches,
    phase1_surface_normalize_session_branch_spines trees = Some branches ->
    map phase1_surface_session_branch_spine_tree branches = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros branches Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst branches.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_session_branch_spine tree)
      as [branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_session_branch_spines rest)
      as [rest_branches |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst branches.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_session_branch_spine_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceStructuredSessionChoiceSpine : Type := {
  phase1_structured_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_structured_session_choice_first_branch :
    Phase1SurfaceSessionBranchSpine;
  phase1_structured_session_choice_rest_branches :
    list Phase1SurfaceSessionBranchSpine
}.

Definition phase1_surface_structured_session_choice_spine_tree
  (choice : Phase1SurfaceStructuredSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_structured_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_session_branch_spine_tree
        (phase1_structured_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_session_branch_spine_tree branch))
          (phase1_structured_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_structured_session_choice_spine
  (choice : Phase1SurfaceSessionChoiceSpine)
  : option Phase1SurfaceStructuredSessionChoiceSpine :=
  match
    phase1_surface_normalize_session_branch_spine
      (phase1_session_choice_first_branch_tree choice),
    phase1_surface_normalize_session_branch_spines
      (phase1_session_choice_rest_branch_trees choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_structured_session_choice_direction :=
             phase1_session_choice_direction choice;
           phase1_structured_session_choice_first_branch := first_branch;
           phase1_structured_session_choice_rest_branches := rest_branches |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_structured_session_choice_spine_round_trip :
  forall choice refined,
    phase1_surface_normalize_structured_session_choice_spine choice =
      Some refined ->
    phase1_surface_structured_session_choice_spine_tree refined =
      phase1_surface_session_choice_spine_tree choice.
Proof.
  intros [direction first_tree rest_trees] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_session_branch_spine first_tree)
    as [first_branch |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_session_branch_spines rest_trees)
    as [rest_branches |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_session_branch_spine_round_trip
      first_tree first_branch Hfirst).
  rewrite
    (phase1_surface_normalize_session_branch_spines_round_trip
      rest_trees rest_branches Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_structured_session_choice_tree
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceStructuredSessionChoiceSpine :=
  match phase1_surface_normalize_session_choice_spine direction tree with
  | Some choice => phase1_surface_normalize_structured_session_choice_spine choice
  | None => None
  end.

Theorem phase1_surface_normalize_structured_session_choice_tree_round_trip :
  forall direction tree refined,
    phase1_surface_normalize_structured_session_choice_tree direction tree =
      Some refined ->
    phase1_surface_structured_session_choice_spine_tree refined = tree.
Proof.
  intros direction tree refined Hnormalize.
  unfold phase1_surface_normalize_structured_session_choice_tree in Hnormalize.
  destruct (phase1_surface_normalize_session_choice_spine direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_session_choice_spine_tree choice).
  - eapply phase1_surface_normalize_structured_session_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_session_choice_spine_round_trip.
    exact Hchoice.
Qed.
