From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstEffectSetSpine
  GrammarAstStaticReferenceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine a single effect_expression.

  The effect label advances to the established static-reference spine. Optional
  term arguments are opened only at their wrapper boundary in this slice: when
  present, the exact certified term_arguments ParseTree is retained for the
  dedicated argument-expression refinement that follows.
*)

Definition phase1_surface_optional_term_arguments_tree
  (arguments : option ParseTree) : ParseTree :=
  match arguments with
  | None => PTOptionalNone
  | Some arguments_tree => PTOptionalSome arguments_tree
  end.

Definition phase1_surface_normalize_optional_term_arguments
  (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some arguments_tree) =>
      match phase1_surface_validate_named_node "term_arguments" arguments_tree with
      | Some tt => Some (Some arguments_tree)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_term_arguments_round_trip :
  forall tree arguments,
    phase1_surface_normalize_optional_term_arguments tree = Some arguments ->
    phase1_surface_optional_term_arguments_tree arguments = tree.
Proof.
  intros tree arguments Hnormalize.
  unfold phase1_surface_normalize_optional_term_arguments in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[arguments_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct
      (phase1_surface_validate_named_node "term_arguments" arguments_tree)
      as [[] |] eqn:Harguments; try discriminate Hnormalize.
    inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_term_arguments_tree.
    rewrite
      (phase1_surface_expect_optional_round_trip
        tree (Some arguments_tree) Hoptional).
    reflexivity.
  - inversion Hnormalize; subst arguments.
    unfold phase1_surface_optional_term_arguments_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceEffectExpressionSpine : Type := {
  phase1_effect_expression_spine_reference :
    Phase1SurfaceStaticReferenceSpine;
  phase1_effect_expression_spine_arguments :
    option ParseTree
}.

Definition phase1_surface_effect_expression_spine_tree
  (effect : Phase1SurfaceEffectExpressionSpine) : ParseTree :=
  PTNonterminal "effect_expression"
    (PTSequence
      [ phase1_surface_static_reference_spine_tree
          (phase1_effect_expression_spine_reference effect);
        phase1_surface_optional_term_arguments_tree
          (phase1_effect_expression_spine_arguments effect)
      ]).

Definition phase1_surface_normalize_effect_expression_spine
  (tree : ParseTree) : option Phase1SurfaceEffectExpressionSpine :=
  match phase1_surface_expect_nonterminal "effect_expression" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (reference_tree, arguments_tree) =>
              match
                phase1_surface_normalize_static_reference_spine reference_tree,
                phase1_surface_normalize_optional_term_arguments arguments_tree
              with
              | Some reference, Some arguments =>
                  Some
                    {| phase1_effect_expression_spine_reference := reference;
                       phase1_effect_expression_spine_arguments := arguments |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_effect_expression_spine_round_trip :
  forall tree effect,
    phase1_surface_normalize_effect_expression_spine tree = Some effect ->
    phase1_surface_effect_expression_spine_tree effect = tree.
Proof.
  intros tree effect Hnormalize.
  unfold phase1_surface_normalize_effect_expression_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "effect_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[reference_tree arguments_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_static_reference_spine reference_tree)
    as [reference |] eqn:Hreference; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_term_arguments arguments_tree)
    as [arguments |] eqn:Harguments; try discriminate Hnormalize.
  inversion Hnormalize; subst effect.
  unfold phase1_surface_effect_expression_spine_tree.
  cbn.
  rewrite
    (phase1_surface_expect_nonterminal_round_trip
      "effect_expression" tree body Hnode).
  rewrite
    (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite
    (phase1_surface_exact2_round_trip
      items reference_tree arguments_tree Hitems).
  rewrite
    (phase1_surface_normalize_static_reference_spine_round_trip
      reference_tree reference Hreference).
  rewrite
    (phase1_surface_normalize_optional_term_arguments_round_trip
      arguments_tree arguments Harguments).
  reflexivity.
Qed.
