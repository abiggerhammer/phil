From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTermArgumentsSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Replace every expression payload in the term-argument list with the
  recursive grouping expression carrier. The existing shell retains exact
  parentheses, comma order, and the distinction between empty and nonempty
  lists. No predecessor list or duplicate ParseTree payload is stored.

  Each argument uses the expression raw normalizer, with no caller-supplied
  fuel. The inherited command, failure-target, and generic grouping nested
  fallback boundaries remain. Enclosing named-postfix and effect carriers are
  not changed by this module, and no production Haskell binding is claimed.
*)

Fixpoint phase1_surface_normalize_term_argument_recursive_grouping_values
  (arguments : list ParseTree)
  : option (list Phase1SurfaceExpressionRecursiveGroupingSpine) :=
  match arguments with
  | [] => Some []
  | argument :: rest =>
      match
        phase1_surface_normalize_expression_recursive_grouping_tree argument,
        phase1_surface_normalize_term_argument_recursive_grouping_values rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_term_argument_recursive_grouping_values_round_trip :
  forall arguments refined,
    phase1_surface_normalize_term_argument_recursive_grouping_values arguments =
      Some refined ->
    map phase1_surface_expression_recursive_grouping_spine_tree refined =
      arguments.
Proof.
  induction arguments as [|argument rest IH]; intros refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn [phase1_surface_normalize_term_argument_recursive_grouping_values]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_recursive_grouping_tree argument)
      as [actual |] eqn:Hargument; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_term_argument_recursive_grouping_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [map].
    rewrite
      (phase1_surface_normalize_expression_recursive_grouping_tree_round_trip
        argument actual Hargument),
      (IH actual_rest eq_refl).
    reflexivity.
Qed.

Record Phase1SurfaceTermArgumentsRecursiveGroupingSpine : Type := {
  phase1_term_arguments_recursive_grouping_spine_arguments :
    list Phase1SurfaceExpressionRecursiveGroupingSpine
}.

Definition phase1_surface_term_arguments_recursive_grouping_spine_base
  (arguments : Phase1SurfaceTermArgumentsRecursiveGroupingSpine)
  : Phase1SurfaceTermArgumentsSpine :=
  {| phase1_term_arguments_spine_arguments :=
       map phase1_surface_expression_recursive_grouping_spine_tree
         (phase1_term_arguments_recursive_grouping_spine_arguments arguments) |}.

Definition phase1_surface_term_arguments_recursive_grouping_spine_tree
  (arguments : Phase1SurfaceTermArgumentsRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_term_arguments_spine_tree
    (phase1_surface_term_arguments_recursive_grouping_spine_base arguments).

Definition phase1_surface_normalize_term_arguments_recursive_grouping_spine
  (previous : Phase1SurfaceTermArgumentsSpine)
  : option Phase1SurfaceTermArgumentsRecursiveGroupingSpine :=
  match phase1_surface_normalize_term_argument_recursive_grouping_values
    (phase1_term_arguments_spine_arguments previous) with
  | Some refined =>
      Some {| phase1_term_arguments_recursive_grouping_spine_arguments :=
                refined |}
  | None => None
  end.

Theorem phase1_surface_normalize_term_arguments_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_term_arguments_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_term_arguments_recursive_grouping_spine_base refined = previous.
Proof.
  intros [arguments] refined Hnormalize.
  unfold phase1_surface_normalize_term_arguments_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_term_arguments_spine_arguments] in Hnormalize.
  destruct
    (phase1_surface_normalize_term_argument_recursive_grouping_values arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_term_arguments_recursive_grouping_spine_base.
  cbn [phase1_term_arguments_recursive_grouping_spine_arguments].
  rewrite
    (phase1_surface_normalize_term_argument_recursive_grouping_values_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_term_arguments_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_term_arguments_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
      phase1_surface_term_arguments_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_term_arguments_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_term_arguments_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Definition phase1_surface_normalize_term_arguments_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceTermArgumentsRecursiveGroupingSpine :=
  match phase1_surface_normalize_term_arguments_spine tree with
  | Some previous =>
      phase1_surface_normalize_term_arguments_recursive_grouping_spine previous
  | None => None
  end.

Theorem phase1_surface_normalize_term_arguments_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_term_arguments_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_term_arguments_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_term_arguments_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_term_arguments_spine tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_term_arguments_spine_tree previous).
  - eapply
      phase1_surface_normalize_term_arguments_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_term_arguments_spine_round_trip.
    exact Hprevious.
Qed.

Definition phase1_surface_refine_term_arguments_recursive_grouping
  (previous : Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option Phase1SurfaceTermArgumentsRecursiveGroupingSpine :=
  phase1_surface_normalize_term_arguments_recursive_grouping_tree
    (phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
      previous).

Theorem phase1_surface_refine_term_arguments_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_term_arguments_recursive_grouping previous =
      Some refined ->
    phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
      phase1_surface_term_arguments_expression_fallback_base_choice_shift_refined_spine_tree
        previous.
Proof.
  intros previous refined Hnormalize.
  exact
    (phase1_surface_normalize_term_arguments_recursive_grouping_tree_round_trip
      _ refined Hnormalize).
Qed.
