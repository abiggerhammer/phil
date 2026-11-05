From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstStaticReferenceSpine
  GrammarAstEffectExpressionSpine
  GrammarAstTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine
  GrammarAstTermArgumentsRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Consume the recursive grouping term-arguments carrier in an effect's actual
  optional argument field. The existing static-reference carrier is copied
  exactly by both shell conversion and the legacy adapter. Argument absence
  remains distinct from a present empty argument list "()".

  No predecessor payload or duplicate argument tree is stored. Static-reference
  interiors and the term-argument carrier's command, failure-target, and nested
  grouping fallback boundaries keep their existing scope. This module does not
  lift the replacement into effect sets or establish production Haskell binding.
*)

Definition phase1_surface_optional_term_arguments_recursive_grouping_tree
  (arguments : option Phase1SurfaceTermArgumentsRecursiveGroupingSpine)
  : ParseTree :=
  phase1_surface_optional_term_arguments_tree
    (option_map phase1_surface_term_arguments_recursive_grouping_spine_tree
      arguments).

Definition phase1_surface_normalize_optional_term_arguments_recursive_grouping
  (previous : option ParseTree)
  : option (option Phase1SurfaceTermArgumentsRecursiveGroupingSpine) :=
  match previous with
  | None => Some None
  | Some arguments_tree =>
      match phase1_surface_normalize_term_arguments_recursive_grouping_tree
        arguments_tree with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_term_arguments_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_normalize_optional_term_arguments_recursive_grouping previous =
      Some refined ->
    option_map phase1_surface_term_arguments_recursive_grouping_spine_tree refined =
      previous.
Proof.
  intros [arguments_tree |] refined Hnormalize.
  - cbn [phase1_surface_normalize_optional_term_arguments_recursive_grouping]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_term_arguments_recursive_grouping_tree arguments_tree)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn [option_map].
    rewrite
      (phase1_surface_normalize_term_arguments_recursive_grouping_tree_round_trip
        arguments_tree actual Harguments).
    reflexivity.
  - inversion Hnormalize; reflexivity.
Qed.

Theorem
  phase1_surface_normalize_optional_term_arguments_recursive_grouping_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_optional_term_arguments_recursive_grouping previous =
      Some refined ->
    phase1_surface_optional_term_arguments_recursive_grouping_tree refined =
      phase1_surface_optional_term_arguments_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_optional_term_arguments_recursive_grouping_tree.
  rewrite
    (phase1_surface_normalize_optional_term_arguments_recursive_grouping_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Record Phase1SurfaceEffectExpressionRecursiveGroupingSpine : Type := {
  phase1_effect_expression_recursive_grouping_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_recursive_grouping_spine_arguments :
    option Phase1SurfaceTermArgumentsRecursiveGroupingSpine
}.

Definition phase1_surface_effect_expression_recursive_grouping_spine_base
  (effect : Phase1SurfaceEffectExpressionRecursiveGroupingSpine)
  : Phase1SurfaceEffectExpressionSpine :=
  {| phase1_effect_expression_spine_reference :=
       phase1_effect_expression_recursive_grouping_spine_reference effect;
     phase1_effect_expression_spine_arguments :=
       option_map phase1_surface_term_arguments_recursive_grouping_spine_tree
         (phase1_effect_expression_recursive_grouping_spine_arguments effect) |}.

Definition phase1_surface_effect_expression_recursive_grouping_spine_tree
  (effect : Phase1SurfaceEffectExpressionRecursiveGroupingSpine) : ParseTree :=
  phase1_surface_effect_expression_spine_tree
    (phase1_surface_effect_expression_recursive_grouping_spine_base effect).

Definition phase1_surface_normalize_effect_expression_recursive_grouping_spine
  (previous : Phase1SurfaceEffectExpressionSpine)
  : option Phase1SurfaceEffectExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_optional_term_arguments_recursive_grouping
    (phase1_effect_expression_spine_arguments previous) with
  | Some arguments =>
      Some
        {| phase1_effect_expression_recursive_grouping_spine_reference :=
             phase1_effect_expression_spine_reference previous;
           phase1_effect_expression_recursive_grouping_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_spine_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_expression_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_expression_recursive_grouping_spine_base refined =
      previous.
Proof.
  intros [reference arguments] refined Hnormalize.
  unfold phase1_surface_normalize_effect_expression_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_effect_expression_spine_reference
    phase1_effect_expression_spine_arguments] in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments_recursive_grouping arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_effect_expression_recursive_grouping_spine_base.
  cbn [phase1_effect_expression_recursive_grouping_spine_reference
    phase1_effect_expression_recursive_grouping_spine_arguments].
  rewrite
    (phase1_surface_normalize_optional_term_arguments_recursive_grouping_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_spine_tree_round_trip :
  forall previous refined,
    phase1_surface_normalize_effect_expression_recursive_grouping_spine previous =
      Some refined ->
    phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
      phase1_surface_effect_expression_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  unfold phase1_surface_effect_expression_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_effect_expression_recursive_grouping_spine_round_trip
      previous refined Hnormalize).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_spine_reference_preserved :
  forall previous refined,
    phase1_surface_normalize_effect_expression_recursive_grouping_spine previous =
      Some refined ->
    phase1_effect_expression_recursive_grouping_spine_reference refined =
      phase1_effect_expression_spine_reference previous.
Proof.
  intros previous refined Hnormalize.
  exact
    (f_equal phase1_effect_expression_spine_reference
      (phase1_surface_normalize_effect_expression_recursive_grouping_spine_round_trip
        previous refined Hnormalize)).
Qed.

Definition phase1_surface_normalize_effect_expression_recursive_grouping_tree
  (tree : ParseTree) : option Phase1SurfaceEffectExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_effect_expression_spine tree with
  | Some previous =>
      phase1_surface_normalize_effect_expression_recursive_grouping_spine previous
  | None => None
  end.

Theorem
  phase1_surface_normalize_effect_expression_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_effect_expression_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_effect_expression_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_effect_expression_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_effect_expression_spine tree)
    as [previous |] eqn:Hprevious; try discriminate Hnormalize.
  transitivity (phase1_surface_effect_expression_spine_tree previous).
  - eapply
      phase1_surface_normalize_effect_expression_recursive_grouping_spine_tree_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_effect_expression_spine_round_trip.
    exact Hprevious.
Qed.

Definition phase1_surface_refine_optional_term_arguments_recursive_grouping
  (previous :
    option Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option (option Phase1SurfaceTermArgumentsRecursiveGroupingSpine) :=
  match previous with
  | None => Some None
  | Some arguments =>
      match phase1_surface_refine_term_arguments_recursive_grouping arguments with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem phase1_surface_refine_optional_term_arguments_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_optional_term_arguments_recursive_grouping previous =
      Some refined ->
    phase1_surface_optional_term_arguments_recursive_grouping_tree refined =
      phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
        previous.
Proof.
  intros [arguments |] refined Hnormalize.
  - cbn [phase1_surface_refine_optional_term_arguments_recursive_grouping]
      in Hnormalize.
    destruct (phase1_surface_refine_term_arguments_recursive_grouping arguments)
      as [actual |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    unfold phase1_surface_optional_term_arguments_recursive_grouping_tree.
    cbn [option_map phase1_surface_optional_term_arguments_tree
      phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree].
    rewrite
      (phase1_surface_refine_term_arguments_recursive_grouping_round_trip
        arguments actual Harguments).
    reflexivity.
  - inversion Hnormalize; reflexivity.
Qed.

Definition phase1_surface_refine_effect_expression_recursive_grouping
  (previous : Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine)
  : option Phase1SurfaceEffectExpressionRecursiveGroupingSpine :=
  match phase1_surface_refine_optional_term_arguments_recursive_grouping
    (phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments
      previous) with
  | Some arguments =>
      Some
        {| phase1_effect_expression_recursive_grouping_spine_reference :=
             phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
               previous;
           phase1_effect_expression_recursive_grouping_spine_arguments :=
             arguments |}
  | None => None
  end.

Theorem phase1_surface_refine_effect_expression_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_effect_expression_recursive_grouping previous =
      Some refined ->
    phase1_surface_effect_expression_recursive_grouping_spine_tree refined =
      phase1_surface_effect_expression_expression_fallback_base_choice_shift_refined_spine_tree
        previous.
Proof.
  intros [reference arguments] refined Hnormalize.
  unfold phase1_surface_refine_effect_expression_recursive_grouping in Hnormalize.
  cbn
    [phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
     phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments]
    in Hnormalize.
  destruct
    (phase1_surface_refine_optional_term_arguments_recursive_grouping arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  change
    (PTNonterminal "effect_expression"
      (PTSequence
        [ phase1_surface_static_reference_spine_tree reference;
          phase1_surface_optional_term_arguments_recursive_grouping_tree actual ]) =
     PTNonterminal "effect_expression"
      (PTSequence
        [ phase1_surface_static_reference_spine_tree reference;
          phase1_surface_optional_term_arguments_expression_fallback_base_choice_shift_refined_tree
            arguments ])).
  rewrite
    (phase1_surface_refine_optional_term_arguments_recursive_grouping_round_trip
      arguments actual Harguments).
  reflexivity.
Qed.

Theorem phase1_surface_refine_effect_expression_recursive_grouping_reference_preserved :
  forall previous refined,
    phase1_surface_refine_effect_expression_recursive_grouping previous =
      Some refined ->
    phase1_effect_expression_recursive_grouping_spine_reference refined =
      phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
        previous.
Proof.
  intros [reference arguments] refined Hnormalize.
  unfold phase1_surface_refine_effect_expression_recursive_grouping in Hnormalize.
  cbn
    [phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_reference
     phase1_effect_expression_expression_fallback_base_choice_shift_refined_spine_arguments]
    in Hnormalize.
  destruct
    (phase1_surface_refine_optional_term_arguments_recursive_grouping arguments)
    as [actual |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; reflexivity.
Qed.
