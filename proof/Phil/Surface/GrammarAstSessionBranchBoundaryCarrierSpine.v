From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchParamsCarrierSpine
  GrammarAstSessionTransferBoundaryCarrierSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional `using static_reference` child inside a parameterized
  session_branch.  The reference reuses the most-refined static-reference
  carrier already established for send/receive boundaries; guards and
  continuations remain at their current exact certified ParseTree boundaries.
*)

Definition phase1_surface_normalize_session_branch_boundary
  (tree : ParseTree)
  : option (option Phase1SurfaceStaticTypeArgumentsReferenceSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (using_tree, reference_tree) =>
              match phase1_surface_expect_literal "using" using_tree,
                    phase1_surface_normalize_static_type_arguments_reference_tree
                      reference_tree
              with
              | Some tt, Some reference => Some (Some reference)
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_boundary_round_trip :
  forall tree boundary,
    phase1_surface_normalize_session_branch_boundary tree = Some boundary ->
    phase1_surface_boundary_refined_annotation_tree boundary = tree.
Proof.
  intros tree boundary Hnormalize.
  unfold phase1_surface_normalize_session_branch_boundary in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[using_tree reference_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "using" using_tree)
      as [[] |] eqn:Husing; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_static_type_arguments_reference_tree reference_tree)
      as [reference |] eqn:Hreference; try discriminate Hnormalize.
    inversion Hnormalize; subst boundary.
    unfold phase1_surface_boundary_refined_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items using_tree reference_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip "using" using_tree Husing).
    rewrite
      (phase1_surface_normalize_static_type_arguments_reference_tree_round_trip
        reference_tree reference Hreference).
    reflexivity.
  - inversion Hnormalize; subst boundary.
    unfold phase1_surface_boundary_refined_annotation_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceBoundaryRefinedSessionBranchSpine : Type := {
  phase1_boundary_refined_session_branch_label : string;
  phase1_boundary_refined_session_branch_params :
    option (list Phase1SurfaceTermParamTypeSpine);
  phase1_boundary_refined_session_branch_boundary :
    option Phase1SurfaceStaticTypeArgumentsReferenceSpine;
  phase1_boundary_refined_session_branch_guard_tree : ParseTree;
  phase1_boundary_refined_session_branch_continuation_tree : ParseTree
}.

Definition phase1_surface_boundary_refined_session_branch_spine_tree
  (branch : Phase1SurfaceBoundaryRefinedSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_boundary_refined_session_branch_label branch);
        phase1_surface_session_branch_params_tree
          (phase1_boundary_refined_session_branch_params branch);
        phase1_surface_boundary_refined_annotation_tree
          (phase1_boundary_refined_session_branch_boundary branch);
        phase1_boundary_refined_session_branch_guard_tree branch;
        PTLiteral "=>";
        phase1_boundary_refined_session_branch_continuation_tree branch
      ]).

Definition phase1_surface_normalize_boundary_refined_session_branch_spine
  (branch : Phase1SurfaceParameterizedSessionBranchSpine)
  : option Phase1SurfaceBoundaryRefinedSessionBranchSpine :=
  match
    phase1_surface_normalize_session_branch_boundary
      (phase1_parameterized_session_branch_boundary_tree branch)
  with
  | Some boundary =>
      Some
        {| phase1_boundary_refined_session_branch_label :=
             phase1_parameterized_session_branch_label branch;
           phase1_boundary_refined_session_branch_params :=
             phase1_parameterized_session_branch_params branch;
           phase1_boundary_refined_session_branch_boundary := boundary;
           phase1_boundary_refined_session_branch_guard_tree :=
             phase1_parameterized_session_branch_guard_tree branch;
           phase1_boundary_refined_session_branch_continuation_tree :=
             phase1_parameterized_session_branch_continuation_tree branch |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_boundary_refined_session_branch_spine_round_trip :
  forall branch refined,
    phase1_surface_normalize_boundary_refined_session_branch_spine branch =
      Some refined ->
    phase1_surface_boundary_refined_session_branch_spine_tree refined =
      phase1_surface_parameterized_session_branch_spine_tree branch.
Proof.
  intros [label params boundary_tree guard_tree continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_session_branch_boundary boundary_tree)
    as [boundary |] eqn:Hboundary; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_session_branch_boundary_round_trip
      boundary_tree boundary Hboundary).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_boundary_refined_session_branch_spines
  (branches : list Phase1SurfaceParameterizedSessionBranchSpine)
  : option (list Phase1SurfaceBoundaryRefinedSessionBranchSpine) :=
  match branches with
  | [] => Some []
  | branch :: rest =>
      match phase1_surface_normalize_boundary_refined_session_branch_spine branch,
            phase1_surface_normalize_boundary_refined_session_branch_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_boundary_refined_session_branch_spines_round_trip :
  forall branches refined,
    phase1_surface_normalize_boundary_refined_session_branch_spines branches =
      Some refined ->
    map phase1_surface_boundary_refined_session_branch_spine_tree refined =
      map phase1_surface_parameterized_session_branch_spine_tree branches.
Proof.
  intros branches.
  induction branches as [|branch rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_boundary_refined_session_branch_spine branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_boundary_refined_session_branch_spines rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_boundary_refined_session_branch_spine_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceBoundaryRefinedSessionChoiceSpine : Type := {
  phase1_boundary_refined_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_boundary_refined_session_choice_first_branch :
    Phase1SurfaceBoundaryRefinedSessionBranchSpine;
  phase1_boundary_refined_session_choice_rest_branches :
    list Phase1SurfaceBoundaryRefinedSessionBranchSpine
}.

Definition phase1_surface_boundary_refined_session_choice_spine_tree
  (choice : Phase1SurfaceBoundaryRefinedSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_boundary_refined_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_boundary_refined_session_branch_spine_tree
        (phase1_boundary_refined_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_boundary_refined_session_branch_spine_tree branch))
          (phase1_boundary_refined_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_boundary_refined_session_choice_spine
  (choice : Phase1SurfaceParameterizedSessionChoiceSpine)
  : option Phase1SurfaceBoundaryRefinedSessionChoiceSpine :=
  match
    phase1_surface_normalize_boundary_refined_session_branch_spine
      (phase1_parameterized_session_choice_first_branch choice),
    phase1_surface_normalize_boundary_refined_session_branch_spines
      (phase1_parameterized_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_boundary_refined_session_choice_direction :=
             phase1_parameterized_session_choice_direction choice;
           phase1_boundary_refined_session_choice_first_branch := first_branch;
           phase1_boundary_refined_session_choice_rest_branches := rest_branches |}
  | _, _ => None
  end.

Theorem
  phase1_surface_normalize_boundary_refined_session_choice_spine_round_trip :
  forall choice refined,
    phase1_surface_normalize_boundary_refined_session_choice_spine choice =
      Some refined ->
    phase1_surface_boundary_refined_session_choice_spine_tree refined =
      phase1_surface_parameterized_session_choice_spine_tree choice.
Proof.
  intros [direction first_branch rest_branches] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_boundary_refined_session_branch_spine first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_boundary_refined_session_branch_spines rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_boundary_refined_session_branch_spine_round_trip
      first_branch refined_first Hfirst).
  rewrite
    (phase1_surface_normalize_boundary_refined_session_branch_spines_round_trip
      rest_branches refined_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_boundary_refined_session_choice_tree
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceBoundaryRefinedSessionChoiceSpine :=
  match
    phase1_surface_normalize_parameterized_session_choice_tree direction tree
  with
  | Some choice =>
      phase1_surface_normalize_boundary_refined_session_choice_spine choice
  | None => None
  end.

Theorem phase1_surface_normalize_boundary_refined_session_choice_tree_round_trip :
  forall direction tree refined,
    phase1_surface_normalize_boundary_refined_session_choice_tree direction tree =
      Some refined ->
    phase1_surface_boundary_refined_session_choice_spine_tree refined = tree.
Proof.
  intros direction tree refined Hnormalize.
  unfold phase1_surface_normalize_boundary_refined_session_choice_tree in Hnormalize.
  destruct
    (phase1_surface_normalize_parameterized_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_parameterized_session_choice_spine_tree choice).
  - eapply phase1_surface_normalize_boundary_refined_session_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_parameterized_session_choice_tree_round_trip.
    exact Hchoice.
Qed.
