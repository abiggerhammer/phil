From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstBaseExpressionChoiceSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Open the next retained runtime-expression boundary:

    fallback = "fail", failure_target | "reject", base_expression ;

  The fail-side failure_target remains an exact certified ParseTree.  The
  reject-side base_expression advances to the certified command/shift choice
  carrier from the preceding slices.
*)

Inductive Phase1SurfaceFallbackBaseChoiceSpine : Type :=
| Phase1FallbackBaseChoiceFail
    (failure_target : ParseTree)
| Phase1FallbackBaseChoiceReject
    (base : Phase1SurfaceBaseExpressionChoiceSpine).

Definition phase1_surface_fallback_base_choice_spine_tree
  (fallback : Phase1SurfaceFallbackBaseChoiceSpine) : ParseTree :=
  match fallback with
  | Phase1FallbackBaseChoiceFail failure_target =>
      PTNonterminal "fallback"
        (PTAlternative 0
          (PTSequence
            [ PTLiteral "fail";
              failure_target
            ]))
  | Phase1FallbackBaseChoiceReject base =>
      PTNonterminal "fallback"
        (PTAlternative 1
          (PTSequence
            [ PTLiteral "reject";
              phase1_surface_base_expression_choice_spine_tree base
            ]))
  end.

Definition phase1_surface_normalize_fallback_base_choice_spine
  (tree : ParseTree) : option Phase1SurfaceFallbackBaseChoiceSpine :=
  match phase1_surface_expect_nonterminal "fallback" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact2 items with
              | Some (keyword_tree, failure_target) =>
                  match phase1_surface_expect_literal "fail" keyword_tree,
                        phase1_surface_validate_named_node
                          "failure_target" failure_target with
                  | Some tt, Some tt =>
                      Some
                        (Phase1FallbackBaseChoiceFail failure_target)
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_expect_sequence selected with
          | Some items =>
              match phase1_surface_exact2 items with
              | Some (keyword_tree, base_tree) =>
                  match phase1_surface_expect_literal "reject" keyword_tree,
                        phase1_surface_normalize_base_expression_choice_spine
                          base_tree with
                  | Some tt, Some base =>
                      Some (Phase1FallbackBaseChoiceReject base)
                  | _, _ => None
                  end
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_fallback_base_choice_spine_round_trip :
  forall tree fallback,
    phase1_surface_normalize_fallback_base_choice_spine tree = Some fallback ->
    phase1_surface_fallback_base_choice_spine_tree fallback = tree.
Proof.
  intros tree fallback Hnormalize.
  unfold phase1_surface_normalize_fallback_base_choice_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "fallback" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_expect_sequence selected)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[keyword_tree failure_target] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "fail" keyword_tree)
      as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
    destruct
      (phase1_surface_validate_named_node "failure_target" failure_target)
      as [[] |] eqn:Htarget; try discriminate Hnormalize.
    inversion Hnormalize; subst fallback.
    unfold phase1_surface_fallback_base_choice_spine_tree.
    rewrite
      (phase1_surface_expect_nonterminal_round_trip
        "fallback" tree body Hnode).
    rewrite
      (phase1_surface_expect_alternative_round_trip
        body 0 selected Halternative).
    rewrite
      (phase1_surface_expect_sequence_round_trip
        selected items Hsequence).
    rewrite
      (phase1_surface_exact2_round_trip
        items keyword_tree failure_target Hitems).
    rewrite
      (phase1_surface_expect_literal_round_trip
        "fail" keyword_tree Hkeyword).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_expect_sequence selected)
        as [items |] eqn:Hsequence; try discriminate Hnormalize.
      destruct (phase1_surface_exact2 items)
        as [[keyword_tree base_tree] |] eqn:Hitems;
        try discriminate Hnormalize.
      destruct (phase1_surface_expect_literal "reject" keyword_tree)
        as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
      destruct
        (phase1_surface_normalize_base_expression_choice_spine base_tree)
        as [base |] eqn:Hbase; try discriminate Hnormalize.
      inversion Hnormalize; subst fallback.
      unfold phase1_surface_fallback_base_choice_spine_tree.
      rewrite
        (phase1_surface_expect_nonterminal_round_trip
          "fallback" tree body Hnode).
      rewrite
        (phase1_surface_expect_alternative_round_trip
          body 1 selected Halternative).
      rewrite
        (phase1_surface_expect_sequence_round_trip
          selected items Hsequence).
      rewrite
        (phase1_surface_exact2_round_trip
          items keyword_tree base_tree Hitems).
      rewrite
        (phase1_surface_expect_literal_round_trip
          "reject" keyword_tree Hkeyword).
      rewrite
        (phase1_surface_normalize_base_expression_choice_spine_round_trip
          base_tree base Hbase).
      reflexivity.
    + discriminate Hnormalize.
Qed.
