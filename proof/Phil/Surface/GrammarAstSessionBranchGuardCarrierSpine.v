From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchBoundaryCarrierSpine
  GrammarAstSessionTransferGuardCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional `when proposition` child inside a boundary-refined
  session_branch.  The proposition reuses the shared precedence carrier
  already established for transfer guards; continuations remain at their
  current exact certified ParseTree boundary.
*)

Definition phase1_surface_normalize_session_branch_guard
  (tree : ParseTree) : option (option Phase1SurfacePropositionSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (when_tree, proposition_tree) =>
              match phase1_surface_expect_literal "when" when_tree,
                    phase1_surface_normalize_proposition_spine proposition_tree
              with
              | Some tt, Some proposition => Some (Some proposition)
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_guard_round_trip :
  forall tree guard,
    phase1_surface_normalize_session_branch_guard tree = Some guard ->
    phase1_surface_guard_refined_annotation_tree guard = tree.
Proof.
  intros tree guard Hnormalize.
  unfold phase1_surface_normalize_session_branch_guard in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[when_tree proposition_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "when" when_tree)
      as [[] |] eqn:Hwhen; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_proposition_spine proposition_tree)
      as [proposition |] eqn:Hproposition; try discriminate Hnormalize.
    inversion Hnormalize; subst guard.
    unfold phase1_surface_guard_refined_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items when_tree proposition_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip "when" when_tree Hwhen).
    rewrite (phase1_surface_normalize_proposition_spine_round_trip
      proposition_tree proposition Hproposition).
    reflexivity.
  - inversion Hnormalize; subst guard.
    unfold phase1_surface_guard_refined_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceGuardRefinedSessionBranchSpine : Type := {
  phase1_guard_refined_session_branch_label : string;
  phase1_guard_refined_session_branch_params :
    option (list Phase1SurfaceTermParamTypeSpine);
  phase1_guard_refined_session_branch_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_guard_refined_session_branch_guard : option Phase1SurfacePropositionSpine;
  phase1_guard_refined_session_branch_continuation_tree : ParseTree
}.

Definition phase1_surface_guard_refined_session_branch_spine_tree
  (branch : Phase1SurfaceGuardRefinedSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_guard_refined_session_branch_label branch);
        phase1_surface_session_branch_params_tree
          (phase1_guard_refined_session_branch_params branch);
        phase1_surface_boundary_refined_annotation_tree
          (phase1_guard_refined_session_branch_boundary branch);
        phase1_surface_guard_refined_annotation_tree
          (phase1_guard_refined_session_branch_guard branch);
        PTLiteral "=>";
        phase1_guard_refined_session_branch_continuation_tree branch
      ]).

Definition phase1_surface_normalize_guard_refined_session_branch_spine
  (branch : Phase1SurfaceBoundaryRefinedSessionBranchSpine)
  : option Phase1SurfaceGuardRefinedSessionBranchSpine :=
  match
    phase1_surface_normalize_session_branch_guard
      (phase1_boundary_refined_session_branch_guard_tree branch)
  with
  | Some guard =>
      Some
        {| phase1_guard_refined_session_branch_label :=
             phase1_boundary_refined_session_branch_label branch;
           phase1_guard_refined_session_branch_params :=
             phase1_boundary_refined_session_branch_params branch;
           phase1_guard_refined_session_branch_boundary :=
             phase1_boundary_refined_session_branch_boundary branch;
           phase1_guard_refined_session_branch_guard := guard;
           phase1_guard_refined_session_branch_continuation_tree :=
             phase1_boundary_refined_session_branch_continuation_tree branch |}
  | None => None
  end.

Theorem phase1_surface_normalize_guard_refined_session_branch_spine_round_trip :
  forall branch refined,
    phase1_surface_normalize_guard_refined_session_branch_spine branch =
      Some refined ->
    phase1_surface_guard_refined_session_branch_spine_tree refined =
      phase1_surface_boundary_refined_session_branch_spine_tree branch.
Proof.
  intros [label params boundary guard_tree continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_session_branch_guard guard_tree)
    as [guard |] eqn:Hguard; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_session_branch_guard_round_trip
      guard_tree guard Hguard).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_guard_refined_session_branch_spines
  (branches : list Phase1SurfaceBoundaryRefinedSessionBranchSpine)
  : option (list Phase1SurfaceGuardRefinedSessionBranchSpine) :=
  match branches with
  | [] => Some []
  | branch :: rest =>
      match phase1_surface_normalize_guard_refined_session_branch_spine branch,
            phase1_surface_normalize_guard_refined_session_branch_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_guard_refined_session_branch_spines_round_trip :
  forall branches refined,
    phase1_surface_normalize_guard_refined_session_branch_spines branches =
      Some refined ->
    map phase1_surface_guard_refined_session_branch_spine_tree refined =
      map phase1_surface_boundary_refined_session_branch_spine_tree branches.
Proof.
  intros branches.
  induction branches as [|branch rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_guard_refined_session_branch_spine branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_guard_refined_session_branch_spines rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_guard_refined_session_branch_spine_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGuardRefinedSessionChoiceSpine : Type := {
  phase1_guard_refined_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_guard_refined_session_choice_first_branch :
    Phase1SurfaceGuardRefinedSessionBranchSpine;
  phase1_guard_refined_session_choice_rest_branches :
    list Phase1SurfaceGuardRefinedSessionBranchSpine
}.

Definition phase1_surface_guard_refined_session_choice_spine_tree
  (choice : Phase1SurfaceGuardRefinedSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_guard_refined_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_guard_refined_session_branch_spine_tree
        (phase1_guard_refined_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_guard_refined_session_branch_spine_tree branch))
          (phase1_guard_refined_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_guard_refined_session_choice_spine
  (choice : Phase1SurfaceBoundaryRefinedSessionChoiceSpine)
  : option Phase1SurfaceGuardRefinedSessionChoiceSpine :=
  match
    phase1_surface_normalize_guard_refined_session_branch_spine
      (phase1_boundary_refined_session_choice_first_branch choice),
    phase1_surface_normalize_guard_refined_session_branch_spines
      (phase1_boundary_refined_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_guard_refined_session_choice_direction :=
             phase1_boundary_refined_session_choice_direction choice;
           phase1_guard_refined_session_choice_first_branch := first_branch;
           phase1_guard_refined_session_choice_rest_branches := rest_branches |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_guard_refined_session_choice_spine_round_trip :
  forall choice refined,
    phase1_surface_normalize_guard_refined_session_choice_spine choice =
      Some refined ->
    phase1_surface_guard_refined_session_choice_spine_tree refined =
      phase1_surface_boundary_refined_session_choice_spine_tree choice.
Proof.
  intros [direction first_branch rest_branches] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_session_branch_spine first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_session_branch_spines rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_guard_refined_session_branch_spine_round_trip
      first_branch refined_first Hfirst).
  rewrite
    (phase1_surface_normalize_guard_refined_session_branch_spines_round_trip
      rest_branches refined_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_guard_refined_session_choice_tree
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceGuardRefinedSessionChoiceSpine :=
  match
    phase1_surface_normalize_boundary_refined_session_choice_tree direction tree
  with
  | Some choice => phase1_surface_normalize_guard_refined_session_choice_spine choice
  | None => None
  end.

Theorem phase1_surface_normalize_guard_refined_session_choice_tree_round_trip :
  forall direction tree refined,
    phase1_surface_normalize_guard_refined_session_choice_tree direction tree =
      Some refined ->
    phase1_surface_guard_refined_session_choice_spine_tree refined = tree.
Proof.
  intros direction tree refined Hnormalize.
  unfold phase1_surface_normalize_guard_refined_session_choice_tree in Hnormalize.
  destruct
    (phase1_surface_normalize_boundary_refined_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_boundary_refined_session_choice_spine_tree choice).
  - eapply phase1_surface_normalize_guard_refined_session_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_boundary_refined_session_choice_tree_round_trip.
    exact Hchoice.
Qed.
