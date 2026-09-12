From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimitiveTypePayloadSpine
  GrammarAstTypeTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the primitive type-payload refinement introduced by #966. *)

Lemma phase1_surface_uint_type_lookup_for_primitive_totality :
  lookupRule "uint_type" phase1_surface_rules =
    Some (ELexicalClass "UINT_TYPE").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_sint_type_lookup_for_primitive_totality :
  lookupRule "sint_type" phase1_surface_rules =
    Some (ELexicalClass "SINT_TYPE").
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_float_type_lookup_for_primitive_totality :
  lookupRule "float_type" phase1_surface_rules =
    Some (EAlternative [ELiteral "F32"; ELiteral "F64"]).
Proof. vm_compute. reflexivity. Qed.

Lemma phase1_surface_normalize_lexical_type_total_from_derivation :
  forall name lexical_class path input rest tree,
    lookupRule name phase1_surface_rules = Some (ELexicalClass lexical_class) ->
    Derives phase1_surface_rules path (ENonterminal name) input rest tree ->
    exists spelling,
      phase1_surface_normalize_lexical_type name lexical_class tree =
        Some spelling /\
      PTNonterminal name (PTLexical lexical_class spelling) = tree.
Proof.
  intros name lexical_class path input rest tree Hlookup_expected Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path name input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite Hlookup_expected in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (lexical_derivation_is_exact
      phase1_surface_rules (descend path (AtNonterminal name))
      lexical_class input rest subtree Hbody)
    as [spelling [tail [_ [_ Hsubtree]]]].
  assert (Hnormalize :
    phase1_surface_normalize_lexical_type name lexical_class tree =
      Some spelling).
  {
    rewrite Htree, Hsubtree.
    unfold phase1_surface_normalize_lexical_type,
      phase1_surface_expect_nonterminal,
      phase1_surface_expect_lexical.
    cbn.
    rewrite String.eqb_refl.
    rewrite String.eqb_refl.
    reflexivity.
  }
  exists spelling.
  split.
  - exact Hnormalize.
  - eapply phase1_surface_normalize_lexical_type_round_trip.
    exact Hnormalize.
Qed.

Lemma phase1_surface_normalize_float_primitive_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "float_type")
      input rest tree ->
    exists value,
      phase1_surface_normalize_float_primitive tree = Some value /\
      phase1_surface_float_primitive_tree value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "float_type" input rest tree Hderive)
    as [body [subtree [Hlookup [Htree Hbody]]]].
  rewrite phase1_surface_float_type_lookup_for_primitive_totality in Hlookup.
  inversion Hlookup; subst body.
  destruct
    (alternative_derivation_names_exact_branch
      phase1_surface_rules
      (descend path (AtNonterminal "float_type"))
      [ELiteral "F32"; ELiteral "F64"]
      input rest subtree Hbody)
    as [index [item [selected [Hnth [Hsubtree Hselected]]]]].
  destruct index as [|index].
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (literal_derivation_is_exact
        phase1_surface_rules _ "F32" _ _ selected Hselected)
      as [tail [_ [_ Hselected_tree]]].
    assert (Hnormalize :
      phase1_surface_normalize_float_primitive tree = Some Phase1Float32).
    {
      rewrite Htree, Hsubtree, Hselected_tree.
      unfold phase1_surface_normalize_float_primitive,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative,
        phase1_surface_expect_literal.
      cbn.
      repeat rewrite String.eqb_refl.
      reflexivity.
    }
    exists Phase1Float32.
    split; first exact Hnormalize.
    eapply phase1_surface_normalize_float_primitive_round_trip.
    exact Hnormalize.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "F64" _ _ selected Hselected)
        as [tail [_ [_ Hselected_tree]]].
      assert (Hnormalize :
        phase1_surface_normalize_float_primitive tree = Some Phase1Float64).
      {
        rewrite Htree, Hsubtree, Hselected_tree.
        unfold phase1_surface_normalize_float_primitive,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative,
          phase1_surface_expect_literal.
        cbn.
        repeat rewrite String.eqb_refl.
        reflexivity.
      }
      exists Phase1Float64.
      split; first exact Hnormalize.
      eapply phase1_surface_normalize_float_primitive_round_trip.
      exact Hnormalize.
    + cbn in Hnth.
      discriminate Hnth.
Qed.

Lemma phase1_surface_normalize_primitive_nonreference_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    exists type_value refined,
      phase1_surface_normalize_nonreference_type_spine tree = Some type_value /\
      phase1_surface_normalize_primitive_nonreference_type_spine type_value =
        Some refined /\
      phase1_surface_primitive_nonreference_type_spine_tree refined = tree.
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
  destruct index as [|index].
  - cbn in Hnth. inversion Hnth; subst item.
    destruct (literal_derivation_is_exact phase1_surface_rules _ "Unit" _ _ selected Hselected)
      as [tail [_ [_ Hselected_tree]]].
    let type_value := constr:(
      {| phase1_nonreference_type_spine_tag := Phase1UnitType;
         phase1_nonreference_type_spine_selected_tree := selected |}) in
    assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
    { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
        phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
      cbn. rewrite String.eqb_refl. reflexivity. }
    assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
      Some Phase1PrimitiveUnitType).
    { cbn. rewrite Hselected_tree. reflexivity. }
    exists type_value, Phase1PrimitiveUnitType. repeat split; try assumption.
    transitivity (phase1_surface_nonreference_type_spine_tree type_value).
    + eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
    + eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
  - destruct index as [|index].
    + cbn in Hnth. inversion Hnth; subst item.
      destruct (literal_derivation_is_exact phase1_surface_rules _ "Bool" _ _ selected Hselected)
        as [tail [_ [_ Hselected_tree]]].
      let type_value := constr:(
        {| phase1_nonreference_type_spine_tag := Phase1BoolType;
           phase1_nonreference_type_spine_selected_tree := selected |}) in
      assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
      { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
          phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
        cbn. rewrite String.eqb_refl. reflexivity. }
      assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
        Some Phase1PrimitiveBoolType).
      { cbn. rewrite Hselected_tree. reflexivity. }
      exists type_value, Phase1PrimitiveBoolType. repeat split; try assumption.
      transitivity (phase1_surface_nonreference_type_spine_tree type_value).
      * eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
      * eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
    + destruct index as [|index].
      * cbn in Hnth. inversion Hnth; subst item.
        destruct (literal_derivation_is_exact phase1_surface_rules _ "Char" _ _ selected Hselected)
          as [tail [_ [_ Hselected_tree]]].
        let type_value := constr:(
          {| phase1_nonreference_type_spine_tag := Phase1CharType;
             phase1_nonreference_type_spine_selected_tree := selected |}) in
        assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
        { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
            phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
          cbn. rewrite String.eqb_refl. reflexivity. }
        assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
          Some Phase1PrimitiveCharType).
        { cbn. rewrite Hselected_tree. reflexivity. }
        exists type_value, Phase1PrimitiveCharType. repeat split; try assumption.
        transitivity (phase1_surface_nonreference_type_spine_tree type_value).
        -- eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
        -- eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
      * destruct index as [|index].
        -- cbn in Hnth. inversion Hnth; subst item.
           destruct (literal_derivation_is_exact phase1_surface_rules _ "String" _ _ selected Hselected)
             as [tail [_ [_ Hselected_tree]]].
           let type_value := constr:(
             {| phase1_nonreference_type_spine_tag := Phase1StringType;
                phase1_nonreference_type_spine_selected_tree := selected |}) in
           assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
           { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
               phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
             cbn. rewrite String.eqb_refl. reflexivity. }
           assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
             Some Phase1PrimitiveStringType).
           { cbn. rewrite Hselected_tree. reflexivity. }
           exists type_value, Phase1PrimitiveStringType. repeat split; try assumption.
           transitivity (phase1_surface_nonreference_type_spine_tree type_value).
           ++ eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
           ++ eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
        -- destruct index as [|index].
           ++ cbn in Hnth. inversion Hnth; subst item.
              destruct (phase1_surface_normalize_lexical_type_total_from_derivation
                "uint_type" "UINT_TYPE" _ _ _ selected
                phase1_surface_uint_type_lookup_for_primitive_totality Hselected)
                as [spelling [Hselected_norm Hselected_round]].
              let type_value := constr:(
                {| phase1_nonreference_type_spine_tag := Phase1UintType;
                   phase1_nonreference_type_spine_selected_tree := selected |}) in
              assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
              { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
                  phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
                cbn. rewrite String.eqb_refl. reflexivity. }
              assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
                Some (Phase1PrimitiveUintType spelling)).
              { cbn. rewrite Hselected_norm. reflexivity. }
              exists type_value, (Phase1PrimitiveUintType spelling). repeat split; try assumption.
              transitivity (phase1_surface_nonreference_type_spine_tree type_value).
              ** eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
              ** eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
           ++ destruct index as [|index].
              ** cbn in Hnth. inversion Hnth; subst item.
                 destruct (phase1_surface_normalize_lexical_type_total_from_derivation
                   "sint_type" "SINT_TYPE" _ _ _ selected
                   phase1_surface_sint_type_lookup_for_primitive_totality Hselected)
                   as [spelling [Hselected_norm Hselected_round]].
                 let type_value := constr:(
                   {| phase1_nonreference_type_spine_tag := Phase1SintType;
                      phase1_nonreference_type_spine_selected_tree := selected |}) in
                 assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
                 { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
                     phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
                   cbn. rewrite String.eqb_refl. reflexivity. }
                 assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
                   Some (Phase1PrimitiveSintType spelling)).
                 { cbn. rewrite Hselected_norm. reflexivity. }
                 exists type_value, (Phase1PrimitiveSintType spelling). repeat split; try assumption.
                 transitivity (phase1_surface_nonreference_type_spine_tree type_value).
                 --- eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
                 --- eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
              ** destruct index as [|index].
                 --- cbn in Hnth. inversion Hnth; subst item.
                     destruct (phase1_surface_normalize_float_primitive_total_from_derivation
                       _ _ _ selected Hselected)
                       as [value [Hselected_norm Hselected_round]].
                     let type_value := constr:(
                       {| phase1_nonreference_type_spine_tag := Phase1FloatType;
                          phase1_nonreference_type_spine_selected_tree := selected |}) in
                     assert (Houter : phase1_surface_normalize_nonreference_type_spine tree = Some type_value).
                     { rewrite Htree, Hsubtree. unfold phase1_surface_normalize_nonreference_type_spine,
                         phase1_surface_expect_nonterminal, phase1_surface_expect_alternative.
                       cbn. rewrite String.eqb_refl. reflexivity. }
                     assert (Hrefine : phase1_surface_normalize_primitive_nonreference_type_spine type_value =
                       Some (Phase1PrimitiveFloatType value)).
                     { cbn. rewrite Hselected_norm. reflexivity. }
                     exists type_value, (Phase1PrimitiveFloatType value). repeat split; try assumption.
                     transitivity (phase1_surface_nonreference_type_spine_tree type_value).
                     +++ eapply phase1_surface_normalize_primitive_nonreference_type_spine_round_trip; exact Hrefine.
                     +++ eapply phase1_surface_normalize_nonreference_type_spine_round_trip; exact Houter.
                 --- destruct index as [|index].
                     +++ cbn in Hnth. inversion Hnth; subst item.
                         let type_value := constr:(
                           {| phase1_nonreference_type_spine_tag := Phase1BytesType;
                              phase1_nonreference_type_spine_selected_tree := selected |}) in
                         exists type_value, (Phase1OpaqueNonreferenceType Phase1BytesType selected).
                         rewrite Htree, Hsubtree. repeat split; reflexivity.
                     +++ destruct index as [|index].
                         *** cbn in Hnth. inversion Hnth; subst item.
                             let type_value := constr:(
                               {| phase1_nonreference_type_spine_tag := Phase1FrameType;
                                  phase1_nonreference_type_spine_selected_tree := selected |}) in
                             exists type_value, (Phase1OpaqueNonreferenceType Phase1FrameType selected).
                             rewrite Htree, Hsubtree. repeat split; reflexivity.
                         *** destruct index as [|index].
                             ---- cbn in Hnth. inversion Hnth; subst item.
                                  let type_value := constr:(
                                    {| phase1_nonreference_type_spine_tag := Phase1ProofType;
                                       phase1_nonreference_type_spine_selected_tree := selected |}) in
                                  exists type_value, (Phase1OpaqueNonreferenceType Phase1ProofType selected).
                                  rewrite Htree, Hsubtree. repeat split; reflexivity.
                             ---- destruct index as [|index].
                                  ++++ cbn in Hnth. inversion Hnth; subst item.
                                       let type_value := constr:(
                                         {| phase1_nonreference_type_spine_tag := Phase1ValidatedType;
                                            phase1_nonreference_type_spine_selected_tree := selected |}) in
                                       exists type_value, (Phase1OpaqueNonreferenceType Phase1ValidatedType selected).
                                       rewrite Htree, Hsubtree. repeat split; reflexivity.
                                  ++++ destruct index as [|index].
                                       ***** cbn in Hnth. inversion Hnth; subst item.
                                             let type_value := constr:(
                                               {| phase1_nonreference_type_spine_tag := Phase1RefinementType;
                                                  phase1_nonreference_type_spine_selected_tree := selected |}) in
                                             exists type_value, (Phase1OpaqueNonreferenceType Phase1RefinementType selected).
                                             rewrite Htree, Hsubtree. repeat split; reflexivity.
                                       ***** destruct index as [|index].
                                             ------ cbn in Hnth. inversion Hnth; subst item.
                                                    let type_value := constr:(
                                                      {| phase1_nonreference_type_spine_tag := Phase1TupleType;
                                                         phase1_nonreference_type_spine_selected_tree := selected |}) in
                                                    exists type_value, (Phase1OpaqueNonreferenceType Phase1TupleType selected).
                                                    rewrite Htree, Hsubtree. repeat split; reflexivity.
                                             ------ cbn in Hnth. discriminate Hnth.
Qed.

Theorem phase1_surface_normalize_primitive_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_primitive_type_tree tree = Some refined /\
      phase1_surface_primitive_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (derives_nonterminal_exposes_body
      phase1_surface_rules path "type_expression" input rest tree Hderive)
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
  - cbn in Hnth. inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_primitive_nonreference_total_from_derivation
        (descend (descend path (AtNonterminal "type_expression")) (AtAlternative 0))
        input rest selected Hselected)
      as [type_value [refined [Houter [Hrefine Hround]]]].
    let outer_type := constr:(Phase1NonreferenceTypeSpine type_value) in
    let result := constr:(Phase1PrimitiveNonreferenceTypeSpine refined) in
    assert (Htype : phase1_surface_normalize_type_spine tree = Some outer_type).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_type_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn. rewrite String.eqb_refl. rewrite Houter. reflexivity.
    }
    assert (Hresult : phase1_surface_normalize_primitive_type_tree tree = Some result).
    {
      unfold phase1_surface_normalize_primitive_type_tree.
      rewrite Htype. cbn. rewrite Hrefine. reflexivity.
    }
    exists result. split; first exact Hresult.
    eapply phase1_surface_normalize_primitive_type_tree_round_trip.
    exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth. inversion Hnth; subst item.
      let outer_type := constr:(Phase1NamedTypeSpine selected) in
      let result := constr:(Phase1PrimitiveNamedTypeSpine selected) in
      assert (Htype : phase1_surface_normalize_type_spine tree = Some outer_type).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn. rewrite String.eqb_refl. reflexivity.
      }
      assert (Hresult : phase1_surface_normalize_primitive_type_tree tree = Some result).
      {
        unfold phase1_surface_normalize_primitive_type_tree.
        rewrite Htype. reflexivity.
      }
      exists result. split; first exact Hresult.
      eapply phase1_surface_normalize_primitive_type_tree_round_trip.
      exact Hresult.
    + cbn in Hnth. discriminate Hnth.
Qed.
