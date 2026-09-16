From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionChoiceBranchCarrierSpine
  GrammarAstSourceHeader.

Import ListNotations.
Open Scope string_scope.

(*
  First semantic child refinement inside session_branch.

  Decode each certified branch label through the reusable identifier carrier,
  while preserving parameters, boundary, guard, and continuation at their
  current exact certified ParseTree boundaries.  The refinement is then
  lifted through the already-structured select/offer branch list.
*)

Record Phase1SurfaceLabeledSessionBranchSpine : Type := {
  phase1_labeled_session_branch_label : string;
  phase1_labeled_session_branch_params_tree : ParseTree;
  phase1_labeled_session_branch_boundary_tree : ParseTree;
  phase1_labeled_session_branch_guard_tree : ParseTree;
  phase1_labeled_session_branch_continuation_tree : ParseTree
}.

Definition phase1_surface_labeled_session_branch_spine_tree
  (branch : Phase1SurfaceLabeledSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_labeled_session_branch_label branch);
        phase1_labeled_session_branch_params_tree branch;
        phase1_labeled_session_branch_boundary_tree branch;
        phase1_labeled_session_branch_guard_tree branch;
        PTLiteral "=>";
        phase1_labeled_session_branch_continuation_tree branch
      ]).

Definition phase1_surface_normalize_labeled_session_branch_spine
  (branch : Phase1SurfaceSessionBranchSpine)
  : option Phase1SurfaceLabeledSessionBranchSpine :=
  match
    phase1_surface_normalize_identifier
      (phase1_session_branch_label_tree branch)
  with
  | Some label =>
      Some
        {| phase1_labeled_session_branch_label := label;
           phase1_labeled_session_branch_params_tree :=
             phase1_session_branch_params_tree branch;
           phase1_labeled_session_branch_boundary_tree :=
             phase1_session_branch_boundary_tree branch;
           phase1_labeled_session_branch_guard_tree :=
             phase1_session_branch_guard_tree branch;
           phase1_labeled_session_branch_continuation_tree :=
             phase1_session_branch_continuation_tree branch |}
  | None => None
  end.

Theorem phase1_surface_normalize_labeled_session_branch_spine_round_trip :
  forall branch refined,
    phase1_surface_normalize_labeled_session_branch_spine branch =
      Some refined ->
    phase1_surface_labeled_session_branch_spine_tree refined =
      phase1_surface_session_branch_spine_tree branch.
Proof.
  intros [label_tree params_tree boundary_tree guard_tree continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_identifier label_tree)
    as [label |] eqn:Hlabel; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_identifier_round_trip
      label_tree label Hlabel).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_labeled_session_branch_spines
  (branches : list Phase1SurfaceSessionBranchSpine)
  : option (list Phase1SurfaceLabeledSessionBranchSpine) :=
  match branches with
  | [] => Some []
  | branch :: rest =>
      match phase1_surface_normalize_labeled_session_branch_spine branch,
            phase1_surface_normalize_labeled_session_branch_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_labeled_session_branch_spines_round_trip :
  forall branches refined,
    phase1_surface_normalize_labeled_session_branch_spines branches =
      Some refined ->
    map phase1_surface_labeled_session_branch_spine_tree refined =
      map phase1_surface_session_branch_spine_tree branches.
Proof.
  intros branches.
  induction branches as [|branch rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_labeled_session_branch_spine branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_labeled_session_branch_spines rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_labeled_session_branch_spine_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceLabeledSessionChoiceSpine : Type := {
  phase1_labeled_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_labeled_session_choice_first_branch :
    Phase1SurfaceLabeledSessionBranchSpine;
  phase1_labeled_session_choice_rest_branches :
    list Phase1SurfaceLabeledSessionBranchSpine
}.

Definition phase1_surface_labeled_session_choice_spine_tree
  (choice : Phase1SurfaceLabeledSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_labeled_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_labeled_session_branch_spine_tree
        (phase1_labeled_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_labeled_session_branch_spine_tree branch))
          (phase1_labeled_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_labeled_session_choice_spine
  (choice : Phase1SurfaceStructuredSessionChoiceSpine)
  : option Phase1SurfaceLabeledSessionChoiceSpine :=
  match
    phase1_surface_normalize_labeled_session_branch_spine
      (phase1_structured_session_choice_first_branch choice),
    phase1_surface_normalize_labeled_session_branch_spines
      (phase1_structured_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_labeled_session_choice_direction :=
             phase1_structured_session_choice_direction choice;
           phase1_labeled_session_choice_first_branch := first_branch;
           phase1_labeled_session_choice_rest_branches := rest_branches |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_labeled_session_choice_spine_round_trip :
  forall choice refined,
    phase1_surface_normalize_labeled_session_choice_spine choice =
      Some refined ->
    phase1_surface_labeled_session_choice_spine_tree refined =
      phase1_surface_structured_session_choice_spine_tree choice.
Proof.
  intros [direction first_branch rest_branches] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_labeled_session_branch_spine first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_labeled_session_branch_spines rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_labeled_session_branch_spine_round_trip
      first_branch refined_first Hfirst).
  rewrite
    (phase1_surface_normalize_labeled_session_branch_spines_round_trip
      rest_branches refined_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_labeled_session_choice_tree
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceLabeledSessionChoiceSpine :=
  match phase1_surface_normalize_structured_session_choice_tree direction tree with
  | Some choice => phase1_surface_normalize_labeled_session_choice_spine choice
  | None => None
  end.

Theorem phase1_surface_normalize_labeled_session_choice_tree_round_trip :
  forall direction tree refined,
    phase1_surface_normalize_labeled_session_choice_tree direction tree =
      Some refined ->
    phase1_surface_labeled_session_choice_spine_tree refined = tree.
Proof.
  intros direction tree refined Hnormalize.
  unfold phase1_surface_normalize_labeled_session_choice_tree in Hnormalize.
  destruct
    (phase1_surface_normalize_structured_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_structured_session_choice_spine_tree choice).
  - eapply phase1_surface_normalize_labeled_session_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_structured_session_choice_tree_round_trip.
    exact Hchoice.
Qed.
