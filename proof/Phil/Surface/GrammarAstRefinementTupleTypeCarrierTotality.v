From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRefinementTupleTypePayloadTotality
  GrammarAstTypeTotality.

Import ListNotations.
Open Scope string_scope.

(* Lift the final nonreference shell converses through the staged type carrier. *)

Lemma phase1_surface_normalize_refinement_tuple_nonreference_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    exists type_value primitive shallow refined,
      phase1_surface_normalize_nonreference_type_spine tree = Some type_value /\
      phase1_surface_normalize_primitive_nonreference_type_spine type_value =
        Some primitive /\
      phase1_surface_normalize_shallow_compound_nonreference_type_spine primitive =
        Some shallow /\
      phase1_surface_normalize_refinement_tuple_nonreference_type_spine shallow =
        Some refined /\
      phase1_surface_refinement_tuple_nonreference_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_shallow_compound_nonreference_total_from_derivation
      path input rest tree Hderive)
    as [type_value [primitive [shallow
        [Houter [Hprimitive [Hshallow Hshallow_tree]]]]]].
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
    as [index [item [branch_tree [Hnth [Hsubtree Hbranch]]]]].
  destruct shallow as
    [prior |index_expression |reference_tree |proposition_tree |payload
    |tag selected].
  - exists type_value, primitive,
      (Phase1ShallowPriorNonreferenceType prior),
      (Phase1RefinementTuplePriorNonreferenceType prior).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hshallow_tree.
  - exists type_value, primitive,
      (Phase1ShallowBytesType index_expression),
      (Phase1RefinementTuplePriorNonreferenceType
        (Phase1ShallowBytesType index_expression)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hshallow_tree.
  - exists type_value, primitive,
      (Phase1ShallowFrameType reference_tree),
      (Phase1RefinementTuplePriorNonreferenceType
        (Phase1ShallowFrameType reference_tree)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hshallow_tree.
  - exists type_value, primitive,
      (Phase1ShallowProofType proposition_tree),
      (Phase1RefinementTuplePriorNonreferenceType
        (Phase1ShallowProofType proposition_tree)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hshallow_tree.
  - exists type_value, primitive,
      (Phase1ShallowValidatedType payload),
      (Phase1RefinementTuplePriorNonreferenceType
        (Phase1ShallowValidatedType payload)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hshallow_tree.
  - destruct tag.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1UnitType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1UnitType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1BoolType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1BoolType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1CharType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1CharType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1StringType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1StringType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1UintType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1UintType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1SintType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1SintType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1FloatType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1FloatType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1BytesType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1BytesType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1FrameType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1FrameType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1ProofType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1ProofType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1ValidatedType selected),
        (Phase1RefinementTupleOpaqueNonreferenceType Phase1ValidatedType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hshallow_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 11 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hshallow_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_refinement_type_spine_total_from_derivation
          _ _ _ selected Hbranch)
        as [refinement [Hselected Hselected_tree]].
      assert (Hrefine :
        phase1_surface_normalize_refinement_tuple_nonreference_type_spine
          (Phase1ShallowOpaqueNonreferenceType Phase1RefinementType selected) =
        Some (Phase1RefinementTupleRefinementType refinement)).
      { cbn. rewrite Hselected. reflexivity. }
      exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1RefinementType selected),
        (Phase1RefinementTupleRefinementType refinement).
      repeat split; try assumption.
      transitivity
        (phase1_surface_shallow_compound_nonreference_type_spine_tree
          (Phase1ShallowOpaqueNonreferenceType Phase1RefinementType selected)).
      * eapply
          phase1_surface_normalize_refinement_tuple_nonreference_type_spine_round_trip.
        exact Hrefine.
      * exact Hshallow_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 12 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hshallow_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_tuple_type_spine_total_from_derivation
          _ _ _ selected Hbranch)
        as [tuple_type [Hselected Hselected_tree]].
      assert (Hrefine :
        phase1_surface_normalize_refinement_tuple_nonreference_type_spine
          (Phase1ShallowOpaqueNonreferenceType Phase1TupleType selected) =
        Some (Phase1RefinementTupleTupleType tuple_type)).
      { cbn. rewrite Hselected. reflexivity. }
      exists type_value, primitive,
        (Phase1ShallowOpaqueNonreferenceType Phase1TupleType selected),
        (Phase1RefinementTupleTupleType tuple_type).
      repeat split; try assumption.
      transitivity
        (phase1_surface_shallow_compound_nonreference_type_spine_tree
          (Phase1ShallowOpaqueNonreferenceType Phase1TupleType selected)).
      * eapply
          phase1_surface_normalize_refinement_tuple_nonreference_type_spine_round_trip.
        exact Hrefine.
      * exact Hshallow_tree.
Qed.

Theorem phase1_surface_normalize_refinement_tuple_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_refinement_tuple_type_tree tree = Some refined /\
      phase1_surface_refinement_tuple_type_spine_tree refined = tree.
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
  - cbn in Hnth.
    inversion Hnth; subst item.
    destruct
      (phase1_surface_normalize_refinement_tuple_nonreference_total_from_derivation
        (descend
          (descend path (AtNonterminal "type_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [type_value [primitive [shallow [refined
          [Houter [Hprimitive [Hshallow [Hrefine Hround]]]]]]]].
    let outer_type := constr:(Phase1NonreferenceTypeSpine type_value) in
    let primitive_type := constr:(Phase1PrimitiveNonreferenceTypeSpine primitive) in
    let shallow_type := constr:(Phase1ShallowCompoundNonreferenceTypeSpine shallow) in
    let result := constr:(Phase1RefinementTupleNonreferenceTypeSpine refined) in
    assert (Htype :
      phase1_surface_normalize_type_spine tree = Some outer_type).
    {
      rewrite Htree, Hsubtree.
      unfold phase1_surface_normalize_type_spine,
        phase1_surface_expect_nonterminal,
        phase1_surface_expect_alternative.
      cbn.
      rewrite String.eqb_refl.
      rewrite Houter.
      reflexivity.
    }
    assert (Hprimitive_type :
      phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
    {
      unfold phase1_surface_normalize_primitive_type_tree.
      rewrite Htype.
      cbn.
      rewrite Hprimitive.
      reflexivity.
    }
    assert (Hshallow_type :
      phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
    {
      unfold phase1_surface_normalize_shallow_compound_type_tree.
      rewrite Hprimitive_type.
      cbn.
      rewrite Hshallow.
      reflexivity.
    }
    assert (Hresult :
      phase1_surface_normalize_refinement_tuple_type_tree tree = Some result).
    {
      unfold phase1_surface_normalize_refinement_tuple_type_tree.
      rewrite Hshallow_type.
      cbn.
      rewrite Hrefine.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply phase1_surface_normalize_refinement_tuple_type_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let outer_type := constr:(Phase1NamedTypeSpine selected) in
      let primitive_type := constr:(Phase1PrimitiveNamedTypeSpine selected) in
      let shallow_type := constr:(Phase1ShallowCompoundNamedTypeSpine selected) in
      let result := constr:(Phase1RefinementTupleNamedTypeSpine selected) in
      assert (Htype :
        phase1_surface_normalize_type_spine tree = Some outer_type).
      {
        rewrite Htree, Hsubtree.
        unfold phase1_surface_normalize_type_spine,
          phase1_surface_expect_nonterminal,
          phase1_surface_expect_alternative.
        cbn.
        rewrite String.eqb_refl.
        reflexivity.
      }
      assert (Hprimitive_type :
        phase1_surface_normalize_primitive_type_tree tree = Some primitive_type).
      {
        unfold phase1_surface_normalize_primitive_type_tree.
        rewrite Htype.
        reflexivity.
      }
      assert (Hshallow_type :
        phase1_surface_normalize_shallow_compound_type_tree tree = Some shallow_type).
      {
        unfold phase1_surface_normalize_shallow_compound_type_tree.
        rewrite Hprimitive_type.
        reflexivity.
      }
      assert (Hresult :
        phase1_surface_normalize_refinement_tuple_type_tree tree = Some result).
      {
        unfold phase1_surface_normalize_refinement_tuple_type_tree.
        rewrite Hshallow_type.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply phase1_surface_normalize_refinement_tuple_type_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
