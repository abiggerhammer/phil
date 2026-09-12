From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstShallowCompoundTypePayloadSpine
  GrammarAstPrimitiveTypePayloadTotality.

Import ListNotations.
Open Scope string_scope.

(* Converse for the shallow compound type-payload refinement introduced by #970. *)

Definition phase1_surface_bytes_payload_expression_for_totality : EbnfExpression :=
  ESequence
    [ ELiteral "Bytes";
      EOptional
        (ESequence
          [ ELiteral "[";
            ENonterminal "expression";
            ELiteral "]"
          ])
    ].

Definition phase1_surface_validated_payload_expression_for_totality : EbnfExpression :=
  ESequence
    [ ELiteral "Validated";
      ELiteral "[";
      ENonterminal "static_reference";
      ELiteral ",";
      ENonterminal "expression";
      ELiteral ",";
      ENonterminal "expression";
      ELiteral "]"
    ].

Lemma phase1_surface_normalize_bytes_payload_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_bytes_payload_expression_for_totality
      input rest tree ->
    exists index_expression,
      phase1_surface_normalize_bytes_payload tree = Some index_expression /\
      phase1_surface_bytes_payload_tree index_expression = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_bytes_payload_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "Bytes";
        EOptional
          (ESequence
            [ ELiteral "[";
              ENonterminal "expression";
              ELiteral "]"
            ])
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "Bytes") _ _ ?keyword_tree,
    Hoptional : Derives phase1_surface_rules _
      (EOptional
        (ESequence
          [ ELiteral "[";
            ENonterminal "expression";
            ELiteral "]"
          ])) _ _ ?optional_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "Bytes" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (optional_derivation_exposes_presence
          phase1_surface_rules _
          (ESequence
            [ ELiteral "[";
              ENonterminal "expression";
              ELiteral "]"
            ])
          _ _ optional_tree Hoptional)
        as [[_ Hnone] | [index_tree [Hsome Hindex]]];
      [ assert (Hnormalize :
          phase1_surface_normalize_bytes_payload tree = Some None);
        [ rewrite Htree, Hkeyword_tree, Hnone;
          unfold phase1_surface_normalize_bytes_payload,
            phase1_surface_expect_sequence,
            phase1_surface_exact2,
            phase1_surface_expect_literal,
            phase1_surface_expect_optional;
          cbn;
          rewrite String.eqb_refl;
          reflexivity
        | exists None;
          split;
          [ exact Hnormalize
          | eapply phase1_surface_normalize_bytes_payload_round_trip;
            exact Hnormalize ] ]
      | destruct
          (derives_sequence_expression_exposes_items
            phase1_surface_rules _
            [ ELiteral "[";
              ENonterminal "expression";
              ELiteral "]"
            ]
            _ _ index_tree Hindex)
          as [index_trees [Hindex_tree Hindex_items]];
        repeat match goal with
        | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
            inversion Hseq; subst; clear Hseq
        end;
        match goal with
        | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
            inversion Hnil; subst; clear Hnil
        end;
        match goal with
        | Hopen : Derives phase1_surface_rules _
            (ELiteral "[") _ _ ?open_tree,
          Hexpression : Derives phase1_surface_rules _
            (ENonterminal "expression") _ _ ?expression_tree,
          Hclose : Derives phase1_surface_rules _
            (ELiteral "]") _ _ ?close_tree |- _ =>
            destruct
              (literal_derivation_is_exact
                phase1_surface_rules _ "[" _ _ open_tree Hopen)
              as [open_tail [_ [_ Hopen_tree]]];
            destruct
              (literal_derivation_is_exact
                phase1_surface_rules _ "]" _ _ close_tree Hclose)
              as [close_tail [_ [_ Hclose_tree]]];
            destruct
              (derives_nonterminal_exposes_body
                phase1_surface_rules _ "expression"
                _ _ expression_tree Hexpression)
              as [expression_body
                  [expression_subtree
                   [Hexpression_lookup
                    [Hexpression_tree Hexpression_body]]]];
            assert (Hnormalize :
              phase1_surface_normalize_bytes_payload tree =
                Some (Some expression_tree));
            [ rewrite Htree, Hkeyword_tree, Hsome, Hindex_tree,
                Hopen_tree, Hexpression_tree, Hclose_tree;
              unfold phase1_surface_normalize_bytes_payload,
                phase1_surface_expect_sequence,
                phase1_surface_exact2,
                phase1_surface_expect_literal,
                phase1_surface_expect_optional,
                phase1_surface_exact3,
                phase1_surface_expect_nonterminal;
              cbn;
              repeat rewrite String.eqb_refl;
              reflexivity
            | exists (Some expression_tree);
              split;
              [ exact Hnormalize
              | eapply phase1_surface_normalize_bytes_payload_round_trip;
                exact Hnormalize ] ]
        end ]
  end.
Qed.

Lemma phase1_surface_normalize_bracketed_child_payload_total_from_derivation :
  forall keyword child_name path input rest tree,
    Derives phase1_surface_rules path
      (ESequence
        [ ELiteral keyword;
          ELiteral "[";
          ENonterminal child_name;
          ELiteral "]"
        ])
      input rest tree ->
    exists child_tree,
      phase1_surface_normalize_bracketed_child_payload
        keyword child_name tree = Some child_tree /\
      phase1_surface_bracketed_child_payload_tree keyword child_tree = tree.
Proof.
  intros keyword child_name path input rest tree Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral keyword;
        ELiteral "[";
        ENonterminal child_name;
        ELiteral "]"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral keyword) _ _ ?keyword_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "[") _ _ ?open_tree,
    Hchild : Derives phase1_surface_rules _
      (ENonterminal child_name) _ _ ?child_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "]") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ keyword _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "[" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "]" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules _ child_name _ _ child_tree Hchild)
        as [child_body [child_subtree [Hchild_lookup [Hchild_tree Hchild_body]]]];
      assert (Hnormalize :
        phase1_surface_normalize_bracketed_child_payload
          keyword child_name tree = Some child_tree);
      [ rewrite Htree, Hkeyword_tree, Hopen_tree, Hchild_tree, Hclose_tree;
        unfold phase1_surface_normalize_bracketed_child_payload,
          phase1_surface_expect_sequence,
          phase1_surface_exact4,
          phase1_surface_expect_literal,
          phase1_surface_expect_nonterminal;
        cbn;
        repeat rewrite String.eqb_refl;
        reflexivity
      | exists child_tree;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_bracketed_child_payload_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_validated_payload_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      phase1_surface_validated_payload_expression_for_totality
      input rest tree ->
    exists payload,
      phase1_surface_normalize_validated_payload tree = Some payload /\
      phase1_surface_validated_payload_tree payload = tree.
Proof.
  intros path input rest tree Hderive.
  unfold phase1_surface_validated_payload_expression_for_totality in Hderive.
  destruct
    (derives_sequence_expression_exposes_items
      phase1_surface_rules path
      [ ELiteral "Validated";
        ELiteral "[";
        ENonterminal "static_reference";
        ELiteral ",";
        ENonterminal "expression";
        ELiteral ",";
        ENonterminal "expression";
        ELiteral "]"
      ]
      input rest tree Hderive)
    as [trees [Htree Hitems]].
  repeat match goal with
  | Hseq : DerivesSequence phase1_surface_rules _ _ (_ :: _) _ _ _ |- _ =>
      inversion Hseq; subst; clear Hseq
  end.
  match goal with
  | Hnil : DerivesSequence phase1_surface_rules _ _ [] _ _ _ |- _ =>
      inversion Hnil; subst; clear Hnil
  end.
  match goal with
  | Hkeyword : Derives phase1_surface_rules _
      (ELiteral "Validated") _ _ ?keyword_tree,
    Hopen : Derives phase1_surface_rules _
      (ELiteral "[") _ _ ?open_tree,
    Hreference : Derives phase1_surface_rules _
      (ENonterminal "static_reference") _ _ ?reference_tree,
    Hfirst_comma : Derives phase1_surface_rules _
      (ELiteral ",") _ _ ?first_comma_tree,
    Hfirst_expression : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?first_expression_tree,
    Hsecond_comma : Derives phase1_surface_rules _
      (ELiteral ",") _ _ ?second_comma_tree,
    Hsecond_expression : Derives phase1_surface_rules _
      (ENonterminal "expression") _ _ ?second_expression_tree,
    Hclose : Derives phase1_surface_rules _
      (ELiteral "]") _ _ ?close_tree |- _ =>
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "Validated" _ _ keyword_tree Hkeyword)
        as [keyword_tail [_ [_ Hkeyword_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "[" _ _ open_tree Hopen)
        as [open_tail [_ [_ Hopen_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ first_comma_tree Hfirst_comma)
        as [first_comma_tail [_ [_ Hfirst_comma_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "," _ _ second_comma_tree Hsecond_comma)
        as [second_comma_tail [_ [_ Hsecond_comma_tree]]];
      destruct
        (literal_derivation_is_exact
          phase1_surface_rules _ "]" _ _ close_tree Hclose)
        as [close_tail [_ [_ Hclose_tree]]];
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules _ "static_reference"
          _ _ reference_tree Hreference)
        as [reference_body
            [reference_subtree
             [Hreference_lookup [Hreference_tree Hreference_body]]]];
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules _ "expression"
          _ _ first_expression_tree Hfirst_expression)
        as [first_expression_body
            [first_expression_subtree
             [Hfirst_expression_lookup
              [Hfirst_expression_tree Hfirst_expression_body]]]];
      destruct
        (derives_nonterminal_exposes_body
          phase1_surface_rules _ "expression"
          _ _ second_expression_tree Hsecond_expression)
        as [second_expression_body
            [second_expression_subtree
             [Hsecond_expression_lookup
              [Hsecond_expression_tree Hsecond_expression_body]]]];
      let payload := constr:(
        {| phase1_validated_payload_reference := reference_tree;
           phase1_validated_payload_first_expression := first_expression_tree;
           phase1_validated_payload_second_expression := second_expression_tree |}) in
      assert (Hnormalize :
        phase1_surface_normalize_validated_payload tree = Some payload);
      [ rewrite Htree, Hkeyword_tree, Hopen_tree, Hreference_tree,
          Hfirst_comma_tree, Hfirst_expression_tree,
          Hsecond_comma_tree, Hsecond_expression_tree, Hclose_tree;
        unfold phase1_surface_normalize_validated_payload,
          phase1_surface_expect_sequence,
          phase1_surface_shallow_exact8,
          phase1_surface_expect_literal,
          phase1_surface_expect_nonterminal;
        cbn;
        repeat rewrite String.eqb_refl;
        reflexivity
      | exists payload;
        split;
        [ exact Hnormalize
        | eapply phase1_surface_normalize_validated_payload_round_trip;
          exact Hnormalize ] ]
  end.
Qed.

Lemma phase1_surface_normalize_shallow_compound_nonreference_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path
      (ENonterminal "nonreference_type_expression") input rest tree ->
    exists type_value primitive refined,
      phase1_surface_normalize_nonreference_type_spine tree = Some type_value /\
      phase1_surface_normalize_primitive_nonreference_type_spine type_value =
        Some primitive /\
      phase1_surface_normalize_shallow_compound_nonreference_type_spine primitive =
        Some refined /\
      phase1_surface_shallow_compound_nonreference_type_spine_tree refined = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_primitive_nonreference_total_from_derivation
      path input rest tree Hderive)
    as [type_value [primitive [Houter [Hprimitive Hprimitive_tree]]]].
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
  destruct primitive as
    [| | | |spelling |spelling |float_value |tag selected].
  - exists type_value, Phase1PrimitiveUnitType,
      (Phase1ShallowPriorNonreferenceType Phase1PrimitiveUnitType).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, Phase1PrimitiveBoolType,
      (Phase1ShallowPriorNonreferenceType Phase1PrimitiveBoolType).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, Phase1PrimitiveCharType,
      (Phase1ShallowPriorNonreferenceType Phase1PrimitiveCharType).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, Phase1PrimitiveStringType,
      (Phase1ShallowPriorNonreferenceType Phase1PrimitiveStringType).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, (Phase1PrimitiveUintType spelling),
      (Phase1ShallowPriorNonreferenceType (Phase1PrimitiveUintType spelling)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, (Phase1PrimitiveSintType spelling),
      (Phase1ShallowPriorNonreferenceType (Phase1PrimitiveSintType spelling)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - exists type_value, (Phase1PrimitiveFloatType float_value),
      (Phase1ShallowPriorNonreferenceType (Phase1PrimitiveFloatType float_value)).
    repeat split; try assumption; try reflexivity.
    cbn. exact Hprimitive_tree.
  - destruct tag.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1UnitType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1UnitType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1BoolType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1BoolType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1CharType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1CharType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1StringType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1StringType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1UintType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1UintType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1SintType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1SintType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1FloatType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1FloatType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 7 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hprimitive_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      change
        (Derives phase1_surface_rules _
          phase1_surface_bytes_payload_expression_for_totality
          _ _ selected) in Hbranch.
      destruct
        (phase1_surface_normalize_bytes_payload_total_from_derivation
          _ _ _ selected Hbranch)
        as [index_expression [Hpayload Hpayload_tree]].
      assert (Hshallow :
        phase1_surface_normalize_shallow_compound_nonreference_type_spine
          (Phase1OpaqueNonreferenceType Phase1BytesType selected) =
        Some (Phase1ShallowBytesType index_expression)).
      { cbn. rewrite Hpayload. reflexivity. }
      exists type_value,
        (Phase1OpaqueNonreferenceType Phase1BytesType selected),
        (Phase1ShallowBytesType index_expression).
      repeat split; try assumption.
      transitivity
        (phase1_surface_primitive_nonreference_type_spine_tree
          (Phase1OpaqueNonreferenceType Phase1BytesType selected)).
      * eapply
          phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip.
        exact Hshallow.
      * exact Hprimitive_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 8 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hprimitive_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_bracketed_child_payload_total_from_derivation
          "Frame" "static_reference" _ _ _ selected Hbranch)
        as [reference_tree [Hpayload Hpayload_tree]].
      assert (Hshallow :
        phase1_surface_normalize_shallow_compound_nonreference_type_spine
          (Phase1OpaqueNonreferenceType Phase1FrameType selected) =
        Some (Phase1ShallowFrameType reference_tree)).
      { cbn. rewrite Hpayload. reflexivity. }
      exists type_value,
        (Phase1OpaqueNonreferenceType Phase1FrameType selected),
        (Phase1ShallowFrameType reference_tree).
      repeat split; try assumption.
      transitivity
        (phase1_surface_primitive_nonreference_type_spine_tree
          (Phase1OpaqueNonreferenceType Phase1FrameType selected)).
      * eapply
          phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip.
        exact Hshallow.
      * exact Hprimitive_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 9 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hprimitive_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      destruct
        (phase1_surface_normalize_bracketed_child_payload_total_from_derivation
          "Proof" "proposition" _ _ _ selected Hbranch)
        as [proposition_tree [Hpayload Hpayload_tree]].
      assert (Hshallow :
        phase1_surface_normalize_shallow_compound_nonreference_type_spine
          (Phase1OpaqueNonreferenceType Phase1ProofType selected) =
        Some (Phase1ShallowProofType proposition_tree)).
      { cbn. rewrite Hpayload. reflexivity. }
      exists type_value,
        (Phase1OpaqueNonreferenceType Phase1ProofType selected),
        (Phase1ShallowProofType proposition_tree).
      repeat split; try assumption.
      transitivity
        (phase1_surface_primitive_nonreference_type_spine_tree
          (Phase1OpaqueNonreferenceType Phase1ProofType selected)).
      * eapply
          phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip.
        exact Hshallow.
      * exact Hprimitive_tree.
    + assert (Hshape :
        PTNonterminal "nonreference_type_expression"
          (PTAlternative 10 selected) =
        PTNonterminal "nonreference_type_expression"
          (PTAlternative index branch_tree)).
      {
        transitivity tree.
        - exact Hprimitive_tree.
        - rewrite Htree, Hsubtree. reflexivity.
      }
      inversion Hshape; subst.
      cbn in Hnth.
      inversion Hnth; subst item.
      change
        (Derives phase1_surface_rules _
          phase1_surface_validated_payload_expression_for_totality
          _ _ selected) in Hbranch.
      destruct
        (phase1_surface_normalize_validated_payload_total_from_derivation
          _ _ _ selected Hbranch)
        as [payload [Hpayload Hpayload_tree]].
      assert (Hshallow :
        phase1_surface_normalize_shallow_compound_nonreference_type_spine
          (Phase1OpaqueNonreferenceType Phase1ValidatedType selected) =
        Some (Phase1ShallowValidatedType payload)).
      { cbn. rewrite Hpayload. reflexivity. }
      exists type_value,
        (Phase1OpaqueNonreferenceType Phase1ValidatedType selected),
        (Phase1ShallowValidatedType payload).
      repeat split; try assumption.
      transitivity
        (phase1_surface_primitive_nonreference_type_spine_tree
          (Phase1OpaqueNonreferenceType Phase1ValidatedType selected)).
      * eapply
          phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip.
        exact Hshallow.
      * exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1RefinementType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1RefinementType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
    + exists type_value,
        (Phase1OpaqueNonreferenceType Phase1TupleType selected),
        (Phase1ShallowOpaqueNonreferenceType Phase1TupleType selected).
      repeat split; try assumption; try reflexivity.
      cbn. exact Hprimitive_tree.
Qed.

Theorem phase1_surface_normalize_shallow_compound_type_tree_total_from_derivation :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "type_expression")
      input rest tree ->
    exists refined,
      phase1_surface_normalize_shallow_compound_type_tree tree = Some refined /\
      phase1_surface_shallow_compound_type_spine_tree refined = tree.
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
      (phase1_surface_normalize_shallow_compound_nonreference_total_from_derivation
        (descend
          (descend path (AtNonterminal "type_expression"))
          (AtAlternative 0))
        input rest selected Hselected)
      as [type_value [primitive [refined
          [Houter [Hprimitive [Hshallow Hround]]]]]].
    let outer_type := constr:(Phase1NonreferenceTypeSpine type_value) in
    let primitive_type := constr:(Phase1PrimitiveNonreferenceTypeSpine primitive) in
    let result := constr:(Phase1ShallowCompoundNonreferenceTypeSpine refined) in
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
    assert (Hresult :
      phase1_surface_normalize_shallow_compound_type_tree tree = Some result).
    {
      unfold phase1_surface_normalize_shallow_compound_type_tree.
      rewrite Hprimitive_type.
      cbn.
      rewrite Hshallow.
      reflexivity.
    }
    exists result.
    split.
    + exact Hresult.
    + eapply phase1_surface_normalize_shallow_compound_type_tree_round_trip.
      exact Hresult.
  - destruct index as [|index].
    + cbn in Hnth.
      inversion Hnth; subst item.
      let outer_type := constr:(Phase1NamedTypeSpine selected) in
      let primitive_type := constr:(Phase1PrimitiveNamedTypeSpine selected) in
      let result := constr:(Phase1ShallowCompoundNamedTypeSpine selected) in
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
      assert (Hresult :
        phase1_surface_normalize_shallow_compound_type_tree tree = Some result).
      {
        unfold phase1_surface_normalize_shallow_compound_type_tree.
        rewrite Hprimitive_type.
        reflexivity.
      }
      exists result.
      split.
      * exact Hresult.
      * eapply phase1_surface_normalize_shallow_compound_type_tree_round_trip.
        exact Hresult.
    + cbn in Hnth.
      discriminate Hnth.
Qed.
