From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarDeterminacySimpleResolverSoundness
  GrammarAstParenthesizedExpressionSpine
  GrammarAstTupleExpressionSpine
  GrammarAstRecursiveGrouping
  GrammarAstRecursiveGroupingTotality
  GrammarAstPrimaryExpressionIntegerSpine
  GrammarAstPrimaryExpressionRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(* PHIL-SURFACE-GRAMMAR-CORR-001.
   Every derived primary expression is accepted using the normalizer's own
   computable fuel bound. The older carrier is used only as an adapter input;
   its grouping payloads are replaced, not stored beside a second view. *)

Lemma phase1_surface_recursive_grouping_parenthesized_result :
  forall fuel body converted,
    phase1_surface_normalize_recursive_grouping_fuel
      fuel (PTNonterminal "parenthesized_expression" body) = Some converted ->
    exists expression, converted = Phase1GroupingParenthesized expression.
Proof.
  intros [|fuel] body converted Hnormalize.
  - discriminate Hnormalize.
  - change
      (match phase1_surface_normalize_parenthesized_expression_spine
        (PTNonterminal "parenthesized_expression" body) with
       | Some grouped =>
           match phase1_surface_grouping_expression_with
             (phase1_surface_normalize_recursive_grouping_fuel fuel)
             (phase1_parenthesized_expression_spine_expression grouped) with
           | Some expression => Some (Phase1GroupingParenthesized expression)
           | None => None
           end
       | None => None
       end = Some converted) in Hnormalize.
    destruct
      (phase1_surface_normalize_parenthesized_expression_spine
        (PTNonterminal "parenthesized_expression" body)) as [grouped |];
      try discriminate Hnormalize.
    destruct
      (phase1_surface_grouping_expression_with
        (phase1_surface_normalize_recursive_grouping_fuel fuel)
        (phase1_parenthesized_expression_spine_expression grouped));
      try discriminate Hnormalize.
    inversion Hnormalize; subst. eauto.
Qed.

Lemma phase1_surface_recursive_grouping_tuple_result :
  forall fuel body converted,
    phase1_surface_normalize_recursive_grouping_fuel
      fuel (PTNonterminal "tuple_expression" body) = Some converted ->
    exists first second rest,
      converted = Phase1GroupingTuple first second rest.
Proof.
  intros [|fuel] body converted Hnormalize.
  - discriminate Hnormalize.
  - change
      (match phase1_surface_normalize_tuple_expression_spine
        (PTNonterminal "tuple_expression" body) with
       | Some tuple =>
           match
             phase1_surface_grouping_expression_with
               (phase1_surface_normalize_recursive_grouping_fuel fuel)
               (phase1_tuple_expression_spine_first tuple),
             phase1_surface_grouping_expression_with
               (phase1_surface_normalize_recursive_grouping_fuel fuel)
               (phase1_tuple_expression_spine_second tuple),
             phase1_surface_grouping_traverse
               (phase1_surface_grouping_expression_with
                 (phase1_surface_normalize_recursive_grouping_fuel fuel))
               (phase1_tuple_expression_spine_rest tuple)
           with
           | Some first, Some second, Some rest =>
               Some (Phase1GroupingTuple first second rest)
           | _, _, _ => None
           end
       | None => None
       end = Some converted) in Hnormalize.
    destruct
      (phase1_surface_normalize_tuple_expression_spine
        (PTNonterminal "tuple_expression" body)) as [tuple |];
      try discriminate Hnormalize.
    destruct
      (phase1_surface_grouping_expression_with
        (phase1_surface_normalize_recursive_grouping_fuel fuel)
        (phase1_tuple_expression_spine_first tuple));
      try discriminate Hnormalize.
    destruct
      (phase1_surface_grouping_expression_with
        (phase1_surface_normalize_recursive_grouping_fuel fuel)
        (phase1_tuple_expression_spine_second tuple));
      try discriminate Hnormalize.
    destruct
      (phase1_surface_grouping_traverse
        (phase1_surface_grouping_expression_with
          (phase1_surface_normalize_recursive_grouping_fuel fuel))
        (phase1_tuple_expression_spine_rest tuple));
      try discriminate Hnormalize.
    inversion Hnormalize; subst. eauto.
Qed.

Lemma phase1_surface_primary_expression_recursive_grouping_normalize_wrapper :
  forall index selected,
    phase1_surface_normalize_primary_expression_recursive_grouping_tree
      (PTNonterminal "primary_expression" (PTAlternative index selected)) =
    match phase1_surface_normalize_recursive_grouping selected with
    | Some converted =>
        phase1_surface_primary_expression_recursive_grouping_branch
          index converted
    | None => None
    end.
Proof.
  intros index selected.
  unfold phase1_surface_normalize_primary_expression_recursive_grouping_tree,
    phase1_surface_normalize_recursive_grouping.
  change
    (match
       (match
          (match phase1_surface_normalize_recursive_grouping_fuel
            (phase1_surface_grouping_tree_size selected) selected with
           | Some converted =>
               Some (Phase1GroupingAlternative index converted)
           | None => None
           end)
        with
        | Some converted =>
            Some (Phase1GroupingNonterminal "primary_expression" converted)
        | None => None
        end)
     with
     | Some converted =>
         phase1_surface_primary_expression_recursive_grouping_from_tree converted
     | None => None
     end =
     match phase1_surface_normalize_recursive_grouping_fuel
       (phase1_surface_grouping_tree_size selected) selected with
     | Some converted =>
         phase1_surface_primary_expression_recursive_grouping_branch
           index converted
     | None => None
     end).
  destruct (phase1_surface_normalize_recursive_grouping_fuel
    (phase1_surface_grouping_tree_size selected) selected); reflexivity.
Qed.

Definition phase1_surface_primary_recursive_grouping_items
  : list EbnfExpression :=
  [ ENonterminal "tuple_expression";
    ENonterminal "parenthesized_expression";
    ELiteral "true";
    ELiteral "false";
    ELiteral "unit";
    ENonterminal "char_literal";
    ENonterminal "runtime_string_literal";
    ENonterminal "float_literal";
    ENonterminal "integer_literal" ].

Lemma phase1_surface_primary_recursive_grouping_lookup :
  lookupRule "primary_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_primary_recursive_grouping_items).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_primary_recursive_grouping_lexical_shape :
  forall name class path input rest tree,
    lookupRule name phase1_surface_rules = Some (ELexicalClass class) ->
    Derives phase1_surface_rules path (ENonterminal name) input rest tree ->
    exists value, tree = PTNonterminal name (PTLexical class value).
Proof.
  intros name class path input rest tree Hlookup Hderive.
  destruct (derives_nonterminal_exposes_body
    phase1_surface_rules path name input rest tree Hderive)
    as [body [subtree [Hbody_lookup [Htree Hbody]]]].
  rewrite Hlookup in Hbody_lookup. inversion Hbody_lookup; subst body.
  destruct (lexical_derivation_is_exact phase1_surface_rules
    (descend path (AtNonterminal name)) class input rest subtree Hbody)
    as [value [tail [_ [_ Hsubtree]]]].
  exists value. rewrite Htree, Hsubtree. reflexivity.
Qed.

Lemma phase1_surface_primary_recursive_grouping_branch_total_from_derivation :
  forall index item path input rest selected,
    nth_error phase1_surface_primary_recursive_grouping_items index = Some item ->
    Derives phase1_surface_rules path item input rest selected ->
    exists converted expression,
      phase1_surface_normalize_recursive_grouping selected = Some converted /\
      phase1_surface_primary_expression_recursive_grouping_branch
        index converted = Some expression.
Proof.
  intros index item path input rest selected Hnth Hderive.
  destruct index as [|[|[|[|[|[|[|[|[|index]]]]]]]]];
    cbn in Hnth; try discriminate Hnth; inversion Hnth; subst.
  - destruct (derives_nonterminal_exposes_body phase1_surface_rules path
      "tuple_expression" input rest selected Hderive)
      as [body [subtree [_ [Hselected _]]]].
    destruct (phase1_surface_recursive_grouping_total_from_derivation
      path _ input rest selected Hderive)
      as [converted [Hnormalize _]].
    pose proof Hnormalize as Hshape. rewrite Hselected in Hshape.
    apply phase1_surface_recursive_grouping_tuple_result in Hshape.
    destruct Hshape as [first [second [more Hshape]]]. subst converted.
    exists (Phase1GroupingTuple first second more),
      (Phase1PrimaryGroupingTuple first second more).
    split; [exact Hnormalize | reflexivity].
  - destruct (derives_nonterminal_exposes_body phase1_surface_rules path
      "parenthesized_expression" input rest selected Hderive)
      as [body [subtree [_ [Hselected _]]]].
    destruct (phase1_surface_recursive_grouping_total_from_derivation
      path _ input rest selected Hderive)
      as [converted [Hnormalize _]].
    pose proof Hnormalize as Hshape. rewrite Hselected in Hshape.
    apply phase1_surface_recursive_grouping_parenthesized_result in Hshape.
    destruct Hshape as [expression Hshape]. subst converted.
    exists (Phase1GroupingParenthesized expression),
      (Phase1PrimaryGroupingParenthesized expression).
    split; [exact Hnormalize | reflexivity].
  - destruct (literal_derivation_is_exact phase1_surface_rules path
      "true" input rest selected Hderive) as [tail [_ [_ Hselected]]].
    subst selected.
    exists (Phase1GroupingLiteral "true"), Phase1PrimaryGroupingTrue.
    split; reflexivity.
  - destruct (literal_derivation_is_exact phase1_surface_rules path
      "false" input rest selected Hderive) as [tail [_ [_ Hselected]]].
    subst selected.
    exists (Phase1GroupingLiteral "false"), Phase1PrimaryGroupingFalse.
    split; reflexivity.
  - destruct (literal_derivation_is_exact phase1_surface_rules path
      "unit" input rest selected Hderive) as [tail [_ [_ Hselected]]].
    subst selected.
    exists (Phase1GroupingLiteral "unit"), Phase1PrimaryGroupingUnit.
    split; reflexivity.
  - assert (Hlookup : lookupRule "char_literal" phase1_surface_rules =
      Some (ELexicalClass "CHAR_LITERAL")) by (vm_compute; reflexivity).
    destruct (phase1_surface_primary_recursive_grouping_lexical_shape
      "char_literal" "CHAR_LITERAL" path input rest selected Hlookup Hderive)
      as [value Hselected]. subst selected.
    exists
      (Phase1GroupingNonterminal "char_literal"
        (Phase1GroupingLexical "CHAR_LITERAL" value)),
      (Phase1PrimaryGroupingChar value).
    split; reflexivity.
  - assert (Hlookup : lookupRule "runtime_string_literal" phase1_surface_rules =
      Some (ELexicalClass "STRING_LITERAL")) by (vm_compute; reflexivity).
    destruct (phase1_surface_primary_recursive_grouping_lexical_shape
      "runtime_string_literal" "STRING_LITERAL" path input rest selected
      Hlookup Hderive) as [value Hselected]. subst selected.
    exists
      (Phase1GroupingNonterminal "runtime_string_literal"
        (Phase1GroupingLexical "STRING_LITERAL" value)),
      (Phase1PrimaryGroupingString value).
    split; reflexivity.
  - assert (Hlookup : lookupRule "float_literal" phase1_surface_rules =
      Some (ELexicalClass "DECIMAL_FLOAT")) by (vm_compute; reflexivity).
    destruct (phase1_surface_primary_recursive_grouping_lexical_shape
      "float_literal" "DECIMAL_FLOAT" path input rest selected Hlookup Hderive)
      as [value Hselected]. subst selected.
    exists
      (Phase1GroupingNonterminal "float_literal"
        (Phase1GroupingLexical "DECIMAL_FLOAT" value)),
      (Phase1PrimaryGroupingFloat value).
    split; reflexivity.
  - assert (Hlookup : lookupRule "integer_literal" phase1_surface_rules =
      Some (ELexicalClass "DECIMAL_INTEGER")) by (vm_compute; reflexivity).
    destruct (phase1_surface_primary_recursive_grouping_lexical_shape
      "integer_literal" "DECIMAL_INTEGER" path input rest selected Hlookup Hderive)
      as [value Hselected]. subst selected.
    exists
      (Phase1GroupingNonterminal "integer_literal"
        (Phase1GroupingLexical "DECIMAL_INTEGER" value)),
      (Phase1PrimaryGroupingInteger value).
    split; reflexivity.
  - destruct index; discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_primary_expression_recursive_grouping_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest tree ->
    exists expression,
      phase1_surface_normalize_primary_expression_recursive_grouping_tree tree =
        Some expression /\
      phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
        tree.
Proof.
  intros path input rest tree Hderive.
  destruct (derives_nonterminal_exposes_body phase1_surface_rules path
    "primary_expression" input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_primary_recursive_grouping_lookup in Hlookup.
  inversion Hlookup; subst body.
  destruct (alternative_derivation_names_exact_branch phase1_surface_rules
    (descend path (AtNonterminal "primary_expression"))
    phase1_surface_primary_recursive_grouping_items input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct (phase1_surface_primary_recursive_grouping_branch_total_from_derivation
    index item _ input rest selected Hnth Hselected)
    as [converted [expression [Hnormalize Hbranch]]].
  assert (Hresult :
    phase1_surface_normalize_primary_expression_recursive_grouping_tree tree =
      Some expression).
  {
    rewrite Htree, Hsubtree.
    rewrite phase1_surface_primary_expression_recursive_grouping_normalize_wrapper.
    rewrite Hnormalize. exact Hbranch.
  }
  exists expression. split.
  - exact Hresult.
  - eapply phase1_surface_normalize_primary_expression_recursive_grouping_tree_round_trip.
    exact Hresult.
Qed.

Theorem phase1_surface_refine_primary_expression_recursive_grouping_total_from_derivation :
  forall path input rest previous,
    Derives phase1_surface_rules path (ENonterminal "primary_expression")
      input rest (phase1_surface_primary_expression_integer_spine_tree previous) ->
    exists expression,
      phase1_surface_refine_primary_expression_recursive_grouping previous =
        Some expression /\
      phase1_surface_primary_expression_recursive_grouping_spine_tree expression =
        phase1_surface_primary_expression_integer_spine_tree previous.
Proof.
  intros path input rest previous Hderive.
  exact
    (phase1_surface_normalize_primary_expression_recursive_grouping_tree_total_from_derivation
      path input rest _ Hderive).
Qed.
