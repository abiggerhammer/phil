From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTypeSpine
  GrammarAstTopLevelTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the first recursive type-expression correspondence layer. *)

Definition phase1_surface_nonreference_type_items_for_totality
  : list EbnfExpression :=
  [ ELiteral "Unit";
    ELiteral "Bool";
    ELiteral "Char";
    ELiteral "String";
    ENonterminal "uint_type";
    ENonterminal "sint_type";
    ENonterminal "float_type";
    ESequence
      [ ELiteral "Bytes";
        EOptional
          (ESequence
            [ ELiteral "[";
              ENonterminal "expression";
              ELiteral "]"
            ])
      ];
    ESequence
      [ ELiteral "Frame";
        ELiteral "[";
        ENonterminal "static_reference";
        ELiteral "]"
      ];
    ESequence
      [ ELiteral "Proof";
        ELiteral "[";
        ENonterminal "proposition";
        ELiteral "]"
      ];
    ESequence
      [ ELiteral "Validated";
        ELiteral "[";
        ENonterminal "static_reference";
        ELiteral ",";
        ENonterminal "expression";
        ELiteral ",";
        ENonterminal "expression";
        ELiteral "]"
      ];
    ENonterminal "refinement_type";
    ENonterminal "tuple_type"
  ].

Definition phase1_surface_type_items_for_totality
  : list EbnfExpression :=
  [ ENonterminal "nonreference_type_expression";
    ENonterminal "named_type"
  ].

Lemma phase1_surface_nonreference_type_lookup_for_totality :
  lookupRule "nonreference_type_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_nonreference_type_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_type_lookup_for_totality :
  lookupRule "type_expression" phase1_surface_rules =
    Some (EAlternative phase1_surface_type_items_for_totality).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma phase1_surface_nonreference_type_item_matches_tag :
  forall index item,
    nth_error phase1_surface_nonreference_type_items_for_totality index = Some item ->
    exists tag,
      phase1_surface_nonreference_type_tag_of_index index = Some tag.
Proof.
  intros index item Hnth.
  destruct index as [|index]; cbn in Hnth.
  - exists Phase1UnitType. reflexivity.
  - destruct index as [|index]; cbn in Hnth.
    + exists Phase1BoolType. reflexivity.
    + destruct index as [|index]; cbn in Hnth.
      * exists Phase1CharType. reflexivity.
      * destruct index as [|index]; cbn in Hnth.
        -- exists Phase1StringType. reflexivity.
        -- destruct index as [|index]; cbn in Hnth.
           ++ exists Phase1UintType. reflexivity.
           ++ destruct index as [|index]; cbn in Hnth.
              ** exists Phase1SintType. reflexivity.
              ** destruct index as [|index]; cbn in Hnth.
                 --- exists Phase1FloatType. reflexivity.
                 --- destruct index as [|index]; cbn in Hnth.
                     +++ exists Phase1BytesType. reflexivity.
                     +++ destruct index as [|index]; cbn in Hnth.
                         *** exists Phase1FrameType. reflexivity.
                         *** destruct index as [|index]; cbn in Hnth.
                             ---- exists Phase1ProofType. reflexivity.
                             ---- destruct index as [|index]; cbn in Hnth.
                                  ++++ exists Phase1ValidatedType. reflexivity.
                                  ++++ destruct index as [|index]; cbn in Hnth.
                                       ***** exists Phase1RefinementType. reflexivity.
                                       ***** destruct index as [|index]; cbn in Hnth.
                                             ------ exists Phase1TupleType. reflexivity.
                                             ------ discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_nonreference_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression")
      input rest tree ->
    exists type_value,
      phase1_surface_normalize_nonreference_type_spine tree = Some type_value /\
      phase1_surface_nonreference_type_spine_tree type_value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "nonreference_type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_nonreference_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "nonreference_type_expression"))
      phase1_surface_nonreference_type_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct
    (phase1_surface_nonreference_type_item_matches_tag index item Hnth)
    as [tag Htag].
  let type_value := constr:(
    {| phase1_nonreference_type_spine_tag := tag;
       phase1_nonreference_type_spine_selected_tree := selected |}) in
  assert (Hnormalize :
    phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
  {
    rewrite Htree.
    rewrite Hsubtree.
    unfold phase1_surface_normalize_nonreference_type_spine,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_alternative.
    cbn.
    rewrite Htag.
    reflexivity.
  }
  exists type_value.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_nonreference_type_spine_round_trip.
    exact Hnormalize.
Qed.

Theorem phase1_surface_normalize_type_spine_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists type_value,
      phase1_surface_normalize_type_spine tree = Some type_value /\
      phase1_surface_type_spine_tree type_value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "type_expression"
      input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_type_lookup_for_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "type_expression"))
      phase1_surface_type_items_for_totality
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_nonreference_type_spine_total_from_derivation
        (descend
          (descend path (AtNonterminal "type_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [nonreference [Hnonreference Hround_trip]].
    let type_value := constr:(Phase1NonreferenceTypeSpine nonreference) in
    assert (Hnormalize :
      phase1_surface_normalize_type_spine tree = Some type_value).
    {
      rewrite Htree.
      rewrite Hsubtree.
      unfold phase1_surface_normalize_type_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite Hnonreference.
      reflexivity.
    }
    exists type_value.
    split.
    + exact Hnormalize.
    + eapply phase1_surface_normalize_type_spine_round_trip.
      exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let type_value := constr:(Phase1NamedTypeSpine selected) in
      assert (Hnormalize :
        phase1_surface_normalize_type_spine tree = Some type_value).
      {
        rewrite Htree.
        rewrite Hsubtree.
        unfold phase1_surface_normalize_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        reflexivity.
      }
      exists type_value.
      split.
      * exact Hnormalize.
      * eapply phase1_surface_normalize_type_spine_round_trip.
        exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
