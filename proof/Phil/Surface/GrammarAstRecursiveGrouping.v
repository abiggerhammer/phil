From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstSourceHeader
  GrammarAstExpressionOuterSpine
  GrammarAstParenthesizedExpressionSpine
  GrammarAstTupleExpressionSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Recursive grouping correspondence for the ordinary expression tree.

  Parenthesized and tuple payloads contain recursively normalized expression
  values. The remaining grammar constructors are traversed without changing
  their spelling, ordering, alternative indices, or optional/list structure.
  Command bodies and fallback bodies remain explicit, exact ParseTree
  boundaries. This is a structural proof carrier, not an executable evaluator
  or a binding to the Haskell production AST.
*)

Inductive Phase1SurfaceRecursiveGroupingTree : Type :=
| Phase1GroupingLiteral (literal : string)
| Phase1GroupingLexical (class lexeme : string)
| Phase1GroupingNonterminal
    (name : string) (body : Phase1SurfaceRecursiveGroupingTree)
| Phase1GroupingSequence (items : list Phase1SurfaceRecursiveGroupingTree)
| Phase1GroupingAlternative
    (index : nat) (body : Phase1SurfaceRecursiveGroupingTree)
| Phase1GroupingOptionalNone
| Phase1GroupingOptionalSome (body : Phase1SurfaceRecursiveGroupingTree)
| Phase1GroupingRepetition (items : list Phase1SurfaceRecursiveGroupingTree)
| Phase1GroupingExpression (expression : Phase1SurfaceRecursiveGroupingExpression)
| Phase1GroupingParenthesized
    (expression : Phase1SurfaceRecursiveGroupingExpression)
| Phase1GroupingTuple
    (first second : Phase1SurfaceRecursiveGroupingExpression)
    (rest : list Phase1SurfaceRecursiveGroupingExpression)
| Phase1GroupingCommandBoundary (body : ParseTree)
| Phase1GroupingFallbackBoundary (body : ParseTree)

with Phase1SurfaceRecursiveGroupingExpression : Type :=
| Phase1GroupingExpressionValue
    (base : Phase1SurfaceRecursiveGroupingTree)
    (fallback : option ParseTree).

Fixpoint phase1_surface_recursive_grouping_tree
  (tree : Phase1SurfaceRecursiveGroupingTree) : ParseTree :=
  match tree with
  | Phase1GroupingLiteral literal => PTLiteral literal
  | Phase1GroupingLexical class lexeme => PTLexical class lexeme
  | Phase1GroupingNonterminal name body =>
      PTNonterminal name (phase1_surface_recursive_grouping_tree body)
  | Phase1GroupingSequence items =>
      PTSequence (map phase1_surface_recursive_grouping_tree items)
  | Phase1GroupingAlternative index body =>
      PTAlternative index (phase1_surface_recursive_grouping_tree body)
  | Phase1GroupingOptionalNone => PTOptionalNone
  | Phase1GroupingOptionalSome body =>
      PTOptionalSome (phase1_surface_recursive_grouping_tree body)
  | Phase1GroupingRepetition items =>
      PTRepetition (map phase1_surface_recursive_grouping_tree items)
  | Phase1GroupingExpression expression =>
      phase1_surface_recursive_grouping_expression_tree expression
  | Phase1GroupingParenthesized expression =>
      PTNonterminal "parenthesized_expression"
        (PTSequence
          [ PTLiteral "(";
            phase1_surface_recursive_grouping_expression_tree expression;
            PTLiteral ")" ])
  | Phase1GroupingTuple first second rest =>
      PTNonterminal "tuple_expression"
        (PTSequence
          [ PTLiteral "(";
            phase1_surface_recursive_grouping_expression_tree first;
            PTLiteral ",";
            phase1_surface_recursive_grouping_expression_tree second;
            PTRepetition
              (map
                (fun expression =>
                  phase1_surface_tuple_expression_suffix_tree
                    (phase1_surface_recursive_grouping_expression_tree
                      expression))
                rest);
            PTLiteral ")" ])
  | Phase1GroupingCommandBoundary body =>
      PTNonterminal "command_expression" body
  | Phase1GroupingFallbackBoundary body =>
      PTNonterminal "fallback" body
  end

with phase1_surface_recursive_grouping_expression_tree
  (expression : Phase1SurfaceRecursiveGroupingExpression) : ParseTree :=
  match expression with
  | Phase1GroupingExpressionValue base fallback =>
      phase1_surface_expression_outer_spine_tree
        {| phase1_expression_outer_spine_base :=
             phase1_surface_recursive_grouping_tree base;
           phase1_expression_outer_spine_fallback := fallback |}
  end.

Fixpoint phase1_surface_grouping_traverse {A B : Type}
  (convert : A -> option B) (items : list A) : option (list B) :=
  match items with
  | [] => Some []
  | item :: rest =>
      match convert item, phase1_surface_grouping_traverse convert rest with
      | Some converted, Some converted_rest =>
          Some (converted :: converted_rest)
      | _, _ => None
      end
  end.

Definition phase1_surface_grouping_expression_with
  (normalize : ParseTree -> option Phase1SurfaceRecursiveGroupingTree)
  (tree : ParseTree) : option Phase1SurfaceRecursiveGroupingExpression :=
  match normalize tree with
  | Some (Phase1GroupingExpression expression) => Some expression
  | _ => None
  end.

Fixpoint phase1_surface_normalize_recursive_grouping_fuel
  (fuel : nat) (tree : ParseTree)
  : option Phase1SurfaceRecursiveGroupingTree :=
  match fuel with
  | O => None
  | S remaining =>
      let next := phase1_surface_normalize_recursive_grouping_fuel remaining in
      match tree with
      | PTLiteral literal => Some (Phase1GroupingLiteral literal)
      | PTLexical class lexeme => Some (Phase1GroupingLexical class lexeme)
      | PTNonterminal name body =>
          if String.eqb name "command_expression" then
            Some (Phase1GroupingCommandBoundary body)
          else if String.eqb name "fallback" then
            Some (Phase1GroupingFallbackBoundary body)
          else if String.eqb name "expression" then
            match phase1_surface_normalize_expression_outer_spine tree with
            | Some expression =>
                match next (phase1_expression_outer_spine_base expression) with
                | Some base =>
                    Some
                      (Phase1GroupingExpression
                        (Phase1GroupingExpressionValue base
                          (phase1_expression_outer_spine_fallback expression)))
                | None => None
                end
            | None => None
            end
          else if String.eqb name "parenthesized_expression" then
            match phase1_surface_normalize_parenthesized_expression_spine tree with
            | Some grouped =>
                match phase1_surface_grouping_expression_with next
                  (phase1_parenthesized_expression_spine_expression grouped) with
                | Some expression =>
                    Some (Phase1GroupingParenthesized expression)
                | None => None
                end
            | None => None
            end
          else if String.eqb name "tuple_expression" then
            match phase1_surface_normalize_tuple_expression_spine tree with
            | Some tuple =>
                match
                  phase1_surface_grouping_expression_with next
                    (phase1_tuple_expression_spine_first tuple),
                  phase1_surface_grouping_expression_with next
                    (phase1_tuple_expression_spine_second tuple),
                  phase1_surface_grouping_traverse
                    (phase1_surface_grouping_expression_with next)
                    (phase1_tuple_expression_spine_rest tuple)
                with
                | Some first, Some second, Some rest =>
                    Some (Phase1GroupingTuple first second rest)
                | _, _, _ => None
                end
            | None => None
            end
          else
            match next body with
            | Some converted => Some (Phase1GroupingNonterminal name converted)
            | None => None
            end
      | PTSequence items =>
          match phase1_surface_grouping_traverse next items with
          | Some converted => Some (Phase1GroupingSequence converted)
          | None => None
          end
      | PTAlternative index body =>
          match next body with
          | Some converted => Some (Phase1GroupingAlternative index converted)
          | None => None
          end
      | PTOptionalNone => Some Phase1GroupingOptionalNone
      | PTOptionalSome body =>
          match next body with
          | Some converted => Some (Phase1GroupingOptionalSome converted)
          | None => None
          end
      | PTRepetition items =>
          match phase1_surface_grouping_traverse next items with
          | Some converted => Some (Phase1GroupingRepetition converted)
          | None => None
          end
      end
  end.

Lemma phase1_surface_grouping_traverse_round_trip {A B : Type} :
  forall (convert : A -> option B) (reconstruct : B -> A) items converted,
    (forall item value, convert item = Some value -> reconstruct value = item) ->
    phase1_surface_grouping_traverse convert items = Some converted ->
    map reconstruct converted = items.
Proof.
  intros convert reconstruct items.
  induction items as [|item rest IH]; intros converted Hconvert Hnormalize.
  - inversion Hnormalize; reflexivity.
  - cbn in Hnormalize.
    destruct (convert item) as [value |] eqn:Hvalue;
      try discriminate Hnormalize.
    destruct (phase1_surface_grouping_traverse convert rest)
      as [values |] eqn:Hvalues; try discriminate Hnormalize.
    inversion Hnormalize; subst converted.
    cbn. rewrite (Hconvert item value Hvalue).
    rewrite (IH values Hconvert eq_refl). reflexivity.
Qed.

Lemma phase1_surface_grouping_expression_with_round_trip :
  forall normalize tree expression,
    (forall original converted,
      normalize original = Some converted ->
      phase1_surface_recursive_grouping_tree converted = original) ->
    phase1_surface_grouping_expression_with normalize tree = Some expression ->
    phase1_surface_recursive_grouping_expression_tree expression = tree.
Proof.
  intros normalize tree expression Hnormalize Hexpression.
  unfold phase1_surface_grouping_expression_with in Hexpression.
  destruct (normalize tree) as [converted |] eqn:Hconverted;
    try discriminate Hexpression.
  destruct converted; try discriminate Hexpression.
  inversion Hexpression; subst.
  exact (Hnormalize _ _ Hconverted).
Qed.

Theorem phase1_surface_normalize_recursive_grouping_fuel_round_trip :
  forall fuel tree converted,
    phase1_surface_normalize_recursive_grouping_fuel fuel tree =
      Some converted ->
    phase1_surface_recursive_grouping_tree converted = tree.
Proof.
  induction fuel as [|fuel IH]; intros tree converted Hnormalize.
  - discriminate Hnormalize.
  - destruct tree as
      [literal |class lexeme |name body |items |index body
      | |body |items]; cbn in Hnormalize.
    + inversion Hnormalize; reflexivity.
    + inversion Hnormalize; reflexivity.
    + destruct (String.eqb name "command_expression") eqn:Hcommand.
      * apply String.eqb_eq in Hcommand; subst name.
        inversion Hnormalize; reflexivity.
      * destruct (String.eqb name "fallback") eqn:Hfallback.
        -- apply String.eqb_eq in Hfallback; subst name.
           inversion Hnormalize; reflexivity.
        -- destruct (String.eqb name "expression") eqn:Hexpression.
           ++ apply String.eqb_eq in Hexpression; subst name.
              destruct
                (phase1_surface_normalize_expression_outer_spine
                  (PTNonterminal "expression" body))
                as [[base fallback] |] eqn:Houter;
                try discriminate Hnormalize.
              cbn in Hnormalize.
              destruct (phase1_surface_normalize_recursive_grouping_fuel fuel base)
                as [normalized_base |] eqn:Hbase;
                try discriminate Hnormalize.
              inversion Hnormalize; subst converted.
              cbn.
              rewrite (IH _ _ Hbase).
              exact
                (phase1_surface_normalize_expression_outer_spine_round_trip
                  _ _ Houter).
           ++ destruct (String.eqb name "parenthesized_expression") eqn:Hparen.
              ** apply String.eqb_eq in Hparen; subst name.
                 destruct
                   (phase1_surface_normalize_parenthesized_expression_spine
                     (PTNonterminal "parenthesized_expression" body))
                   as [[nested] |] eqn:Hgrouped;
                   try discriminate Hnormalize.
                 cbn in Hnormalize.
                 destruct
                   (phase1_surface_grouping_expression_with
                     (phase1_surface_normalize_recursive_grouping_fuel fuel)
                     nested)
                   as [expression |] eqn:Hnested;
                   try discriminate Hnormalize.
                 inversion Hnormalize; subst converted.
                 cbn.
                 rewrite
                   (phase1_surface_grouping_expression_with_round_trip
                     _ _ _ IH Hnested).
                 exact
                   (phase1_surface_normalize_parenthesized_expression_spine_round_trip
                     _ _ Hgrouped).
              ** destruct (String.eqb name "tuple_expression") eqn:Htuple.
                 --- apply String.eqb_eq in Htuple; subst name.
                     destruct
                       (phase1_surface_normalize_tuple_expression_spine
                         (PTNonterminal "tuple_expression" body))
                       as [[first second rest] |] eqn:Htuple_shape;
                       try discriminate Hnormalize.
                     cbn in Hnormalize.
                     destruct
                       (phase1_surface_grouping_expression_with
                         (phase1_surface_normalize_recursive_grouping_fuel fuel)
                         first)
                       as [first_value |] eqn:Hfirst;
                       try discriminate Hnormalize.
                     destruct
                       (phase1_surface_grouping_expression_with
                         (phase1_surface_normalize_recursive_grouping_fuel fuel)
                         second)
                       as [second_value |] eqn:Hsecond;
                       try discriminate Hnormalize.
                     destruct
                       (phase1_surface_grouping_traverse
                         (phase1_surface_grouping_expression_with
                           (phase1_surface_normalize_recursive_grouping_fuel fuel))
                         rest)
                       as [rest_values |] eqn:Hrest;
                       try discriminate Hnormalize.
                     inversion Hnormalize; subst converted.
                     cbn.
                     rewrite
                       (phase1_surface_grouping_expression_with_round_trip
                         _ _ _ IH Hfirst),
                       (phase1_surface_grouping_expression_with_round_trip
                         _ _ _ IH Hsecond).
                     assert (Hrest_tree :
                       map phase1_surface_recursive_grouping_expression_tree
                         rest_values = rest).
                     { eapply phase1_surface_grouping_traverse_round_trip.
                       - intros original value Hvalue.
                         eapply phase1_surface_grouping_expression_with_round_trip.
                         + exact IH.
                         + exact Hvalue.
                       - exact Hrest. }
                     rewrite <- map_map, Hrest_tree.
                     exact
                       (phase1_surface_normalize_tuple_expression_spine_round_trip
                         _ _ Htuple_shape).
                 --- destruct
                       (phase1_surface_normalize_recursive_grouping_fuel fuel body)
                       as [normalized_body |] eqn:Hbody;
                       try discriminate Hnormalize.
                     inversion Hnormalize; subst converted.
                     cbn. rewrite (IH _ _ Hbody). reflexivity.
    + destruct
        (phase1_surface_grouping_traverse
          (phase1_surface_normalize_recursive_grouping_fuel fuel) items)
        as [normalized_items |] eqn:Hitems;
        try discriminate Hnormalize.
      inversion Hnormalize; subst converted.
      cbn. f_equal.
      eapply phase1_surface_grouping_traverse_round_trip; eauto.
    + destruct (phase1_surface_normalize_recursive_grouping_fuel fuel body)
        as [normalized_body |] eqn:Hbody;
        try discriminate Hnormalize.
      inversion Hnormalize; subst converted.
      cbn. rewrite (IH _ _ Hbody). reflexivity.
    + inversion Hnormalize; reflexivity.
    + destruct (phase1_surface_normalize_recursive_grouping_fuel fuel body)
        as [normalized_body |] eqn:Hbody;
        try discriminate Hnormalize.
      inversion Hnormalize; subst converted.
      cbn. rewrite (IH _ _ Hbody). reflexivity.
    + destruct
        (phase1_surface_grouping_traverse
          (phase1_surface_normalize_recursive_grouping_fuel fuel) items)
        as [normalized_items |] eqn:Hitems;
        try discriminate Hnormalize.
      inversion Hnormalize; subst converted.
      cbn. f_equal.
      eapply phase1_surface_grouping_traverse_round_trip; eauto.
Qed.

Lemma phase1_surface_recursive_grouping_expression_result :
  forall fuel body converted,
    phase1_surface_normalize_recursive_grouping_fuel
      fuel (PTNonterminal "expression" body) = Some converted ->
    exists expression, converted = Phase1GroupingExpression expression.
Proof.
  intros [|fuel] body converted Hnormalize.
  - discriminate Hnormalize.
  - change
      (match phase1_surface_normalize_expression_outer_spine
        (PTNonterminal "expression" body) with
       | Some outer =>
           match phase1_surface_normalize_recursive_grouping_fuel fuel
             (phase1_expression_outer_spine_base outer) with
           | Some base =>
               Some (Phase1GroupingExpression
                 (Phase1GroupingExpressionValue base
                   (phase1_expression_outer_spine_fallback outer)))
           | None => None
           end
       | None => None
       end = Some converted) in Hnormalize.
    destruct
      (phase1_surface_normalize_expression_outer_spine
        (PTNonterminal "expression" body)) as [outer |];
      try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_recursive_grouping_fuel fuel
        (phase1_expression_outer_spine_base outer));
      try discriminate Hnormalize.
    inversion Hnormalize; subst. eauto.
Qed.

Definition phase1_surface_normalize_recursive_grouping_expression_fuel
  (fuel : nat) (tree : ParseTree)
  : option Phase1SurfaceRecursiveGroupingExpression :=
  phase1_surface_grouping_expression_with
    (phase1_surface_normalize_recursive_grouping_fuel fuel) tree.

Definition phase1_surface_refine_expression_outer_grouping_fuel
  (fuel : nat) (expression : Phase1SurfaceExpressionOuterSpine)
  : option Phase1SurfaceRecursiveGroupingExpression :=
  phase1_surface_normalize_recursive_grouping_expression_fuel fuel
    (phase1_surface_expression_outer_spine_tree expression).

Theorem phase1_surface_refine_expression_outer_grouping_fuel_round_trip :
  forall fuel expression refined,
    phase1_surface_refine_expression_outer_grouping_fuel fuel expression =
      Some refined ->
    phase1_surface_recursive_grouping_expression_tree refined =
      phase1_surface_expression_outer_spine_tree expression.
Proof.
  intros fuel expression refined Hrefined.
  eapply phase1_surface_grouping_expression_with_round_trip.
  - apply phase1_surface_normalize_recursive_grouping_fuel_round_trip.
  - exact Hrefined.
Qed.
