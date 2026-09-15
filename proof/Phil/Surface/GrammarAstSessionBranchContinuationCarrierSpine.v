From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchGuardCarrierSpine
  GrammarAstSessionTransferRecursiveClosureSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the final exact child inside a structured session_branch: its
  continuation session_expression.

  The continuation reuses the recursively closed send/receive session carrier
  from #1028/#1031.  That carrier transitively follows send/receive `then`
  continuations while preserving select/offer/end/recursive/continue payloads
  at their current exact boundaries.  This layer is fuel-indexed for the same
  reason as that reusable recursive carrier.
*)

Record Phase1SurfaceContinuationRefinedSessionBranchSpine : Type := {
  phase1_continuation_refined_session_branch_label : string;
  phase1_continuation_refined_session_branch_params :
    option (list Phase1SurfaceTermParamTypeSpine);
  phase1_continuation_refined_session_branch_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_continuation_refined_session_branch_guard :
    option Phase1SurfacePropositionSpine;
  phase1_continuation_refined_session_branch_continuation :
    Phase1SurfaceRecursiveTransferSessionSpine
}.

Definition phase1_surface_continuation_refined_session_branch_spine_tree
  (branch : Phase1SurfaceContinuationRefinedSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_continuation_refined_session_branch_label branch);
        phase1_surface_session_branch_params_tree
          (phase1_continuation_refined_session_branch_params branch);
        phase1_surface_boundary_refined_annotation_tree
          (phase1_continuation_refined_session_branch_boundary branch);
        phase1_surface_guard_refined_annotation_tree
          (phase1_continuation_refined_session_branch_guard branch);
        PTLiteral "=>";
        phase1_surface_recursive_transfer_session_spine_tree
          (phase1_continuation_refined_session_branch_continuation branch)
      ]).

Definition phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
  (fuel : nat)
  (branch : Phase1SurfaceGuardRefinedSessionBranchSpine)
  : option Phase1SurfaceContinuationRefinedSessionBranchSpine :=
  match
    phase1_surface_normalize_recursive_transfer_session_tree_fuel fuel
      (phase1_guard_refined_session_branch_continuation_tree branch)
  with
  | Some continuation =>
      Some
        {| phase1_continuation_refined_session_branch_label :=
             phase1_guard_refined_session_branch_label branch;
           phase1_continuation_refined_session_branch_params :=
             phase1_guard_refined_session_branch_params branch;
           phase1_continuation_refined_session_branch_boundary :=
             phase1_guard_refined_session_branch_boundary branch;
           phase1_continuation_refined_session_branch_guard :=
             phase1_guard_refined_session_branch_guard branch;
           phase1_continuation_refined_session_branch_continuation :=
             continuation |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_round_trip :
  forall fuel branch refined,
    phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      fuel branch = Some refined ->
    phase1_surface_continuation_refined_session_branch_spine_tree refined =
      phase1_surface_guard_refined_session_branch_spine_tree branch.
Proof.
  intros fuel [label params boundary guard continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel
      fuel continuation_tree)
    as [continuation |] eqn:Hcontinuation; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_recursive_transfer_session_tree_fuel_round_trip
      fuel continuation_tree continuation Hcontinuation).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
  (fuel : nat)
  (branches : list Phase1SurfaceGuardRefinedSessionBranchSpine)
  : option (list Phase1SurfaceContinuationRefinedSessionBranchSpine) :=
  match branches with
  | [] => Some []
  | branch :: rest =>
      match
        phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
          fuel branch,
        phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
          fuel rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_round_trip :
  forall fuel branches refined,
    phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      fuel branches = Some refined ->
    map phase1_surface_continuation_refined_session_branch_spine_tree refined =
      map phase1_surface_guard_refined_session_branch_spine_tree branches.
Proof.
  intros fuel branches.
  induction branches as [|branch rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
        fuel branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
        fuel rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceContinuationRefinedSessionChoiceSpine : Type := {
  phase1_continuation_refined_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_continuation_refined_session_choice_first_branch :
    Phase1SurfaceContinuationRefinedSessionBranchSpine;
  phase1_continuation_refined_session_choice_rest_branches :
    list Phase1SurfaceContinuationRefinedSessionBranchSpine
}.

Definition phase1_surface_continuation_refined_session_choice_spine_tree
  (choice : Phase1SurfaceContinuationRefinedSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_continuation_refined_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_continuation_refined_session_branch_spine_tree
        (phase1_continuation_refined_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_continuation_refined_session_branch_spine_tree
                branch))
          (phase1_continuation_refined_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
  (fuel : nat)
  (choice : Phase1SurfaceGuardRefinedSessionChoiceSpine)
  : option Phase1SurfaceContinuationRefinedSessionChoiceSpine :=
  match
    phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      fuel (phase1_guard_refined_session_choice_first_branch choice),
    phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      fuel (phase1_guard_refined_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_continuation_refined_session_choice_direction :=
             phase1_guard_refined_session_choice_direction choice;
           phase1_continuation_refined_session_choice_first_branch :=
             first_branch;
           phase1_continuation_refined_session_choice_rest_branches :=
             rest_branches |}
  | _, _ => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_session_choice_spine_fuel_round_trip :
  forall fuel choice refined,
    phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
      fuel choice = Some refined ->
    phase1_surface_continuation_refined_session_choice_spine_tree refined =
      phase1_surface_guard_refined_session_choice_spine_tree choice.
Proof.
  intros fuel [direction first_branch rest_branches] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel
      fuel first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel
      fuel rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_continuation_refined_session_branch_spine_fuel_round_trip
      fuel first_branch refined_first Hfirst).
  rewrite
    (phase1_surface_normalize_continuation_refined_session_branch_spines_fuel_round_trip
      fuel rest_branches refined_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
  (fuel : nat)
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree)
  : option Phase1SurfaceContinuationRefinedSessionChoiceSpine :=
  match phase1_surface_normalize_guard_refined_session_choice_tree direction tree with
  | Some choice =>
      phase1_surface_normalize_continuation_refined_session_choice_spine_fuel
        fuel choice
  | None => None
  end.

Theorem
  phase1_surface_normalize_continuation_refined_session_choice_tree_fuel_round_trip :
  forall fuel direction tree refined,
    phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
      fuel direction tree = Some refined ->
    phase1_surface_continuation_refined_session_choice_spine_tree refined = tree.
Proof.
  intros fuel direction tree refined Hnormalize.
  unfold phase1_surface_normalize_continuation_refined_session_choice_tree_fuel
    in Hnormalize.
  destruct
    (phase1_surface_normalize_guard_refined_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_guard_refined_session_choice_spine_tree choice).
  - eapply
      phase1_surface_normalize_continuation_refined_session_choice_spine_fuel_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_guard_refined_session_choice_tree_round_trip.
    exact Hchoice.
Qed.
