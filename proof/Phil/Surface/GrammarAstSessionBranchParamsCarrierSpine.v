From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSessionBranchLabelCarrierSpine
  GrammarAstTermParamTypeSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the optional session_branch parameter clause after branch-label
  correspondence has been closed.

  The semantic carrier is [option (list Phase1SurfaceTermParamTypeSpine)]:
  [None] means that no parenthesized parameter clause was written, while
  [Some []] preserves an explicit empty [()].  Nonempty lists reuse the
  already-closed term_param correspondence.
*)

Definition phase1_surface_session_branch_term_param_suffix_tree
  (parameter : Phase1SurfaceTermParamTypeSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_term_param_type_spine_tree parameter
    ].

Definition phase1_surface_normalize_session_branch_term_param_suffix
  (tree : ParseTree) : option Phase1SurfaceTermParamTypeSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, parameter_tree) =>
          match phase1_surface_expect_literal "," comma_tree with
          | Some tt =>
              phase1_surface_normalize_term_param_type_spine parameter_tree
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_term_param_suffix_round_trip :
  forall tree parameter,
    phase1_surface_normalize_session_branch_term_param_suffix tree =
      Some parameter ->
    phase1_surface_session_branch_term_param_suffix_tree parameter = tree.
Proof.
  intros tree parameter Hnormalize.
  unfold phase1_surface_normalize_session_branch_term_param_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree parameter_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  pose proof
    (phase1_surface_normalize_term_param_type_spine_round_trip
      parameter_tree parameter Hnormalize) as Hparameter.
  unfold phase1_surface_session_branch_term_param_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree parameter_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  rewrite Hparameter.
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_session_branch_term_param_suffixes
  (trees : list ParseTree) : option (list Phase1SurfaceTermParamTypeSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_session_branch_term_param_suffix tree,
            phase1_surface_normalize_session_branch_term_param_suffixes rest with
      | Some parameter, Some parameters => Some (parameter :: parameters)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_session_branch_term_param_suffixes_round_trip :
  forall trees parameters,
    phase1_surface_normalize_session_branch_term_param_suffixes trees =
      Some parameters ->
    map phase1_surface_session_branch_term_param_suffix_tree parameters = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros parameters Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst parameters.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_session_branch_term_param_suffix tree)
      as [parameter |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_session_branch_term_param_suffixes rest)
      as [rest_parameters |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst parameters.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_session_branch_term_param_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_session_branch_term_param_list_tree
  (parameters : list Phase1SurfaceTermParamTypeSpine) : ParseTree :=
  match parameters with
  | [] => PTOptionalNone
  | first :: rest =>
      PTOptionalSome
        (PTSequence
          [ phase1_surface_term_param_type_spine_tree first;
            PTRepetition
              (map phase1_surface_session_branch_term_param_suffix_tree rest)
          ])
  end.

Definition phase1_surface_normalize_session_branch_term_param_list
  (tree : ParseTree) : option (list Phase1SurfaceTermParamTypeSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some []
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (first_tree, rest_tree) =>
              match phase1_surface_expect_repetition rest_tree with
              | Some rest_trees =>
                  match
                    phase1_surface_normalize_term_param_type_spine first_tree,
                    phase1_surface_normalize_session_branch_term_param_suffixes
                      rest_trees
                  with
                  | Some first, Some rest => Some (first :: rest)
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_term_param_list_round_trip :
  forall tree parameters,
    phase1_surface_normalize_session_branch_term_param_list tree =
      Some parameters ->
    phase1_surface_session_branch_term_param_list_tree parameters = tree.
Proof.
  intros tree parameters Hnormalize.
  unfold phase1_surface_normalize_session_branch_term_param_list in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[first_tree rest_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_repetition rest_tree)
      as [rest_trees |] eqn:Hrepetition; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_term_param_type_spine first_tree)
      as [first |] eqn:Hfirst; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_session_branch_term_param_suffixes rest_trees)
      as [rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst parameters.
    unfold phase1_surface_session_branch_term_param_list_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items first_tree rest_tree Hitems).
    rewrite
      (phase1_surface_normalize_term_param_type_spine_round_trip
        first_tree first Hfirst).
    rewrite (phase1_surface_expect_repetition_round_trip
      rest_tree rest_trees Hrepetition).
    rewrite
      (phase1_surface_normalize_session_branch_term_param_suffixes_round_trip
        rest_trees rest Hrest).
    reflexivity.
  - inversion Hnormalize; subst parameters.
    unfold phase1_surface_session_branch_term_param_list_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Definition phase1_surface_session_branch_params_tree
  (parameters : option (list Phase1SurfaceTermParamTypeSpine)) : ParseTree :=
  match parameters with
  | None => PTOptionalNone
  | Some values =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral "(";
            phase1_surface_session_branch_term_param_list_tree values;
            PTLiteral ")"
          ])
  end.

Definition phase1_surface_normalize_session_branch_params
  (tree : ParseTree)
  : option (option (list Phase1SurfaceTermParamTypeSpine)) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact3 items with
          | Some (open_tree, parameters_tree, close_tree) =>
              match phase1_surface_expect_literal "(" open_tree,
                    phase1_surface_normalize_session_branch_term_param_list
                      parameters_tree,
                    phase1_surface_expect_literal ")" close_tree
              with
              | Some tt, Some parameters, Some tt => Some (Some parameters)
              | _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_session_branch_params_round_trip :
  forall tree parameters,
    phase1_surface_normalize_session_branch_params tree = Some parameters ->
    phase1_surface_session_branch_params_tree parameters = tree.
Proof.
  intros tree parameters Hnormalize.
  unfold phase1_surface_normalize_session_branch_params in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact3 items)
      as [[[open_tree parameters_tree] close_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "(" open_tree)
      as [[] |] eqn:Hopen; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_session_branch_term_param_list parameters_tree)
      as [values |] eqn:Hparameters; try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal ")" close_tree)
      as [[] |] eqn:Hclose; try discriminate Hnormalize.
    inversion Hnormalize; subst parameters.
    unfold phase1_surface_session_branch_params_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact3_round_trip
      items open_tree parameters_tree close_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
    rewrite
      (phase1_surface_normalize_session_branch_term_param_list_round_trip
        parameters_tree values Hparameters).
    rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
    reflexivity.
  - inversion Hnormalize; subst parameters.
    unfold phase1_surface_session_branch_params_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceParameterizedSessionBranchSpine : Type := {
  phase1_parameterized_session_branch_label : string;
  phase1_parameterized_session_branch_params :
    option (list Phase1SurfaceTermParamTypeSpine);
  phase1_parameterized_session_branch_boundary_tree : ParseTree;
  phase1_parameterized_session_branch_guard_tree : ParseTree;
  phase1_parameterized_session_branch_continuation_tree : ParseTree
}.

Definition phase1_surface_parameterized_session_branch_spine_tree
  (branch : Phase1SurfaceParameterizedSessionBranchSpine) : ParseTree :=
  PTNonterminal "session_branch"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_parameterized_session_branch_label branch);
        phase1_surface_session_branch_params_tree
          (phase1_parameterized_session_branch_params branch);
        phase1_parameterized_session_branch_boundary_tree branch;
        phase1_parameterized_session_branch_guard_tree branch;
        PTLiteral "=>";
        phase1_parameterized_session_branch_continuation_tree branch
      ]).

Definition phase1_surface_normalize_parameterized_session_branch_spine
  (branch : Phase1SurfaceLabeledSessionBranchSpine)
  : option Phase1SurfaceParameterizedSessionBranchSpine :=
  match
    phase1_surface_normalize_session_branch_params
      (phase1_labeled_session_branch_params_tree branch)
  with
  | Some parameters =>
      Some
        {| phase1_parameterized_session_branch_label :=
             phase1_labeled_session_branch_label branch;
           phase1_parameterized_session_branch_params := parameters;
           phase1_parameterized_session_branch_boundary_tree :=
             phase1_labeled_session_branch_boundary_tree branch;
           phase1_parameterized_session_branch_guard_tree :=
             phase1_labeled_session_branch_guard_tree branch;
           phase1_parameterized_session_branch_continuation_tree :=
             phase1_labeled_session_branch_continuation_tree branch |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_parameterized_session_branch_spine_round_trip :
  forall branch refined,
    phase1_surface_normalize_parameterized_session_branch_spine branch =
      Some refined ->
    phase1_surface_parameterized_session_branch_spine_tree refined =
      phase1_surface_labeled_session_branch_spine_tree branch.
Proof.
  intros [label params_tree boundary_tree guard_tree continuation_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_session_branch_params params_tree)
    as [parameters |] eqn:Hparameters; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_session_branch_params_round_trip
      params_tree parameters Hparameters).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_parameterized_session_branch_spines
  (branches : list Phase1SurfaceLabeledSessionBranchSpine)
  : option (list Phase1SurfaceParameterizedSessionBranchSpine) :=
  match branches with
  | [] => Some []
  | branch :: rest =>
      match phase1_surface_normalize_parameterized_session_branch_spine branch,
            phase1_surface_normalize_parameterized_session_branch_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_parameterized_session_branch_spines_round_trip :
  forall branches refined,
    phase1_surface_normalize_parameterized_session_branch_spines branches =
      Some refined ->
    map phase1_surface_parameterized_session_branch_spine_tree refined =
      map phase1_surface_labeled_session_branch_spine_tree branches.
Proof.
  intros branches.
  induction branches as [|branch rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_parameterized_session_branch_spine branch)
      as [refined_branch |] eqn:Hbranch; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_parameterized_session_branch_spines rest)
      as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_parameterized_session_branch_spine_round_trip.
      exact Hbranch.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceParameterizedSessionChoiceSpine : Type := {
  phase1_parameterized_session_choice_direction :
    Phase1SurfaceSessionChoiceDirection;
  phase1_parameterized_session_choice_first_branch :
    Phase1SurfaceParameterizedSessionBranchSpine;
  phase1_parameterized_session_choice_rest_branches :
    list Phase1SurfaceParameterizedSessionBranchSpine
}.

Definition phase1_surface_parameterized_session_choice_spine_tree
  (choice : Phase1SurfaceParameterizedSessionChoiceSpine) : ParseTree :=
  PTSequence
    [ PTLiteral
        (phase1_surface_session_choice_keyword
          (phase1_parameterized_session_choice_direction choice));
      PTLiteral "{";
      phase1_surface_parameterized_session_branch_spine_tree
        (phase1_parameterized_session_choice_first_branch choice);
      PTRepetition
        (map
          (fun branch =>
            phase1_surface_session_branch_suffix_tree
              (phase1_surface_parameterized_session_branch_spine_tree branch))
          (phase1_parameterized_session_choice_rest_branches choice));
      PTLiteral "}"
    ].

Definition phase1_surface_normalize_parameterized_session_choice_spine
  (choice : Phase1SurfaceLabeledSessionChoiceSpine)
  : option Phase1SurfaceParameterizedSessionChoiceSpine :=
  match
    phase1_surface_normalize_parameterized_session_branch_spine
      (phase1_labeled_session_choice_first_branch choice),
    phase1_surface_normalize_parameterized_session_branch_spines
      (phase1_labeled_session_choice_rest_branches choice)
  with
  | Some first_branch, Some rest_branches =>
      Some
        {| phase1_parameterized_session_choice_direction :=
             phase1_labeled_session_choice_direction choice;
           phase1_parameterized_session_choice_first_branch := first_branch;
           phase1_parameterized_session_choice_rest_branches := rest_branches |}
  | _, _ => None
  end.

Theorem
  phase1_surface_normalize_parameterized_session_choice_spine_round_trip :
  forall choice refined,
    phase1_surface_normalize_parameterized_session_choice_spine choice =
      Some refined ->
    phase1_surface_parameterized_session_choice_spine_tree refined =
      phase1_surface_labeled_session_choice_spine_tree choice.
Proof.
  intros [direction first_branch rest_branches] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_parameterized_session_branch_spine first_branch)
    as [refined_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_parameterized_session_branch_spines rest_branches)
    as [refined_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_parameterized_session_branch_spine_round_trip
      first_branch refined_first Hfirst).
  rewrite
    (phase1_surface_normalize_parameterized_session_branch_spines_round_trip
      rest_branches refined_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_parameterized_session_choice_tree
  (direction : Phase1SurfaceSessionChoiceDirection)
  (tree : ParseTree) : option Phase1SurfaceParameterizedSessionChoiceSpine :=
  match phase1_surface_normalize_labeled_session_choice_tree direction tree with
  | Some choice =>
      phase1_surface_normalize_parameterized_session_choice_spine choice
  | None => None
  end.

Theorem phase1_surface_normalize_parameterized_session_choice_tree_round_trip :
  forall direction tree refined,
    phase1_surface_normalize_parameterized_session_choice_tree direction tree =
      Some refined ->
    phase1_surface_parameterized_session_choice_spine_tree refined = tree.
Proof.
  intros direction tree refined Hnormalize.
  unfold phase1_surface_normalize_parameterized_session_choice_tree in Hnormalize.
  destruct (phase1_surface_normalize_labeled_session_choice_tree direction tree)
    as [choice |] eqn:Hchoice; try discriminate Hnormalize.
  transitivity (phase1_surface_labeled_session_choice_spine_tree choice).
  - eapply phase1_surface_normalize_parameterized_session_choice_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_labeled_session_choice_tree_round_trip.
    exact Hchoice.
Qed.
