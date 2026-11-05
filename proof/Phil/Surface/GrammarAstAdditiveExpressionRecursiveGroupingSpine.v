From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstAdditiveExpressionSpine
  GrammarAstAdditiveExpressionRefinedSpine
  GrammarAstMultiplicativeExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Consume recursive grouping multiplicative values in the leading additive operand
  and every repeated suffix right operand. The existing operator constructors
  and suffix order are retained exactly; no predecessor carrier or duplicate
  tree is stored in the replacement.

  Raw normalization uses the existing shallow shell and the lower layer's
  computed-fuel entry point. The legacy adapter normalizes the old full
  carrier's erasure, so no shared caller-supplied fuel is needed.

  This is structural correspondence. It neither changes evaluation semantics
  nor lifts the replacement into enclosing declaration carriers or Haskell.
  The lower carrier's named-argument, command, and fallback boundaries remain.
*)

Record Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine : Type := {
  phase1_additive_suffix_recursive_grouping_spine_operator :
    Phase1SurfaceAdditiveOperatorSpine;
  phase1_additive_suffix_recursive_grouping_spine_right :
    Phase1SurfaceMultiplicativeExpressionRecursiveGroupingSpine
}.

Definition phase1_surface_additive_suffix_recursive_grouping_spine_base
  (suffix : Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine)
  : Phase1SurfaceAdditiveSuffixSpine :=
  {| phase1_additive_suffix_spine_operator :=
       phase1_additive_suffix_recursive_grouping_spine_operator suffix;
     phase1_additive_suffix_spine_right :=
       phase1_surface_multiplicative_expression_recursive_grouping_spine_tree
         (phase1_additive_suffix_recursive_grouping_spine_right suffix) |}.

Definition phase1_surface_additive_suffix_recursive_grouping_spine_tree
  (suffix : Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine)
  : ParseTree :=
  phase1_surface_additive_suffix_spine_tree
    (phase1_surface_additive_suffix_recursive_grouping_spine_base suffix).

Definition phase1_surface_normalize_additive_suffix_recursive_grouping_spine
  (suffix : Phase1SurfaceAdditiveSuffixSpine)
  : option Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine :=
  match
    phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree
      (phase1_additive_suffix_spine_right suffix)
  with
  | Some right_operand =>
      Some
        {| phase1_additive_suffix_recursive_grouping_spine_operator :=
             phase1_additive_suffix_spine_operator suffix;
           phase1_additive_suffix_recursive_grouping_spine_right :=
             right_operand |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_additive_suffix_recursive_grouping_spine_round_trip :
  forall suffix refined,
    phase1_surface_normalize_additive_suffix_recursive_grouping_spine
      suffix = Some refined ->
    phase1_surface_additive_suffix_recursive_grouping_spine_base refined =
      suffix.
Proof.
  intros [operator right_tree] refined Hnormalize.
  unfold phase1_surface_normalize_additive_suffix_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_additive_suffix_spine_right
    phase1_additive_suffix_spine_operator] in Hnormalize.
  destruct
    (phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree right_tree)
    as [right |] eqn:Hright; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_additive_suffix_recursive_grouping_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree_round_trip
      right_tree right Hright).
  reflexivity.
Qed.

Theorem
  phase1_surface_normalize_additive_suffix_recursive_grouping_spine_tree_round_trip :
  forall suffix refined,
    phase1_surface_normalize_additive_suffix_recursive_grouping_spine
      suffix = Some refined ->
    phase1_surface_additive_suffix_recursive_grouping_spine_tree refined =
      phase1_surface_additive_suffix_spine_tree suffix.
Proof.
  intros suffix refined Hnormalize.
  unfold phase1_surface_additive_suffix_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_additive_suffix_recursive_grouping_spine_round_trip
      suffix refined Hnormalize).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_additive_suffix_recursive_grouping_spines
  (suffixes : list Phase1SurfaceAdditiveSuffixSpine)
  : option (list Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine) :=
  match suffixes with
  | [] => Some []
  | suffix :: rest =>
      match
        phase1_surface_normalize_additive_suffix_recursive_grouping_spine
          suffix,
        phase1_surface_normalize_additive_suffix_recursive_grouping_spines
          rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_additive_suffix_recursive_grouping_spines_round_trip :
  forall suffixes refined,
    phase1_surface_normalize_additive_suffix_recursive_grouping_spines
      suffixes = Some refined ->
    map phase1_surface_additive_suffix_recursive_grouping_spine_base
      refined = suffixes.
Proof.
  induction suffixes as [|suffix rest IH]; intros refined Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn [phase1_surface_normalize_additive_suffix_recursive_grouping_spines]
      in Hnormalize.
    destruct
      (phase1_surface_normalize_additive_suffix_recursive_grouping_spine
        suffix)
      as [head |] eqn:Hhead; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_additive_suffix_recursive_grouping_spines
        rest)
      as [tail |] eqn:Htail; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_additive_suffix_recursive_grouping_spine_round_trip
        suffix head Hhead),
      (IH tail eq_refl).
    reflexivity.
Qed.

Record Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine : Type := {
  phase1_additive_expression_recursive_grouping_spine_first :
    Phase1SurfaceMultiplicativeExpressionRecursiveGroupingSpine;
  phase1_additive_expression_recursive_grouping_spine_rest :
    list Phase1SurfaceAdditiveSuffixRecursiveGroupingSpine
}.

Definition phase1_surface_additive_expression_recursive_grouping_spine_base
  (expression : Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine)
  : Phase1SurfaceAdditiveExpressionSpine :=
  {| phase1_additive_expression_spine_first :=
       phase1_surface_multiplicative_expression_recursive_grouping_spine_tree
         (phase1_additive_expression_recursive_grouping_spine_first
           expression);
     phase1_additive_expression_spine_rest :=
       map phase1_surface_additive_suffix_recursive_grouping_spine_base
         (phase1_additive_expression_recursive_grouping_spine_rest
           expression) |}.

Definition phase1_surface_additive_expression_recursive_grouping_spine_tree
  (expression : Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine)
  : ParseTree :=
  phase1_surface_additive_expression_spine_tree
    (phase1_surface_additive_expression_recursive_grouping_spine_base
      expression).

Definition phase1_surface_normalize_additive_expression_recursive_grouping_spine
  (expression : Phase1SurfaceAdditiveExpressionSpine)
  : option Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine :=
  match
    phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree
      (phase1_additive_expression_spine_first expression),
    phase1_surface_normalize_additive_suffix_recursive_grouping_spines
      (phase1_additive_expression_spine_rest expression)
  with
  | Some first, Some rest =>
      Some
        {| phase1_additive_expression_recursive_grouping_spine_first :=
             first;
           phase1_additive_expression_recursive_grouping_spine_rest :=
             rest |}
  | _, _ => None
  end.

Theorem
  phase1_surface_normalize_additive_expression_recursive_grouping_spine_round_trip :
  forall expression refined,
    phase1_surface_normalize_additive_expression_recursive_grouping_spine
      expression = Some refined ->
    phase1_surface_additive_expression_recursive_grouping_spine_base
      refined = expression.
Proof.
  intros [first_tree suffixes] refined Hnormalize.
  unfold phase1_surface_normalize_additive_expression_recursive_grouping_spine
    in Hnormalize.
  cbn [phase1_additive_expression_spine_first
    phase1_additive_expression_spine_rest] in Hnormalize.
  destruct
    (phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree first_tree)
    as [first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_additive_suffix_recursive_grouping_spines
      suffixes)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_additive_expression_recursive_grouping_spine_base.
  cbn.
  rewrite
    (phase1_surface_normalize_multiplicative_expression_recursive_grouping_tree_round_trip
      first_tree first Hfirst),
    (phase1_surface_normalize_additive_suffix_recursive_grouping_spines_round_trip
      suffixes rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_additive_expression_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine :=
  match phase1_surface_normalize_additive_expression_spine tree with
  | Some expression =>
      phase1_surface_normalize_additive_expression_recursive_grouping_spine
        expression
  | None => None
  end.

Theorem
  phase1_surface_normalize_additive_expression_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_additive_expression_recursive_grouping_tree
      tree = Some refined ->
    phase1_surface_additive_expression_recursive_grouping_spine_tree
      refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_additive_expression_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_additive_expression_spine tree)
    as [expression |] eqn:Hexpression; try discriminate Hnormalize.
  unfold phase1_surface_additive_expression_recursive_grouping_spine_tree.
  rewrite
    (phase1_surface_normalize_additive_expression_recursive_grouping_spine_round_trip
      expression refined Hnormalize).
  exact
    (phase1_surface_normalize_additive_expression_spine_round_trip
      tree expression Hexpression).
Qed.

Definition phase1_surface_refine_additive_expression_recursive_grouping
  (previous : Phase1SurfaceAdditiveExpressionRefinedSpine)
  : option Phase1SurfaceAdditiveExpressionRecursiveGroupingSpine :=
  phase1_surface_normalize_additive_expression_recursive_grouping_tree
    (phase1_surface_additive_expression_refined_spine_tree previous).

Theorem phase1_surface_refine_additive_expression_recursive_grouping_round_trip :
  forall previous refined,
    phase1_surface_refine_additive_expression_recursive_grouping previous =
      Some refined ->
    phase1_surface_additive_expression_recursive_grouping_spine_tree
      refined =
      phase1_surface_additive_expression_refined_spine_tree previous.
Proof.
  intros previous refined Hnormalize.
  exact
    (phase1_surface_normalize_additive_expression_recursive_grouping_tree_round_trip
      _ refined Hnormalize).
Qed.
