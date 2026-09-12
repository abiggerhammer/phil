From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstPrimitiveTypePayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Shallow compound payload refinement below the primitive type layer.

  Bytes, Frame, Proof, and Validated have their concrete wrappers normalized
  here while their recursive children remain exact certified ParseTree values.
  Refinement, tuple, and named/static-reference structure remain for successor
  slices.
*)

Definition phase1_surface_bytes_payload_tree
  (index_expression : option ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral "Bytes";
      match index_expression with
      | None => PTOptionalNone
      | Some expression_tree =>
          PTOptionalSome
            (PTSequence
              [ PTLiteral "[";
                expression_tree;
                PTLiteral "]"
              ])
      end
    ].

Definition phase1_surface_normalize_bytes_payload
  (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (keyword_tree, optional_tree) =>
          match phase1_surface_expect_literal "Bytes" keyword_tree,
                phase1_surface_expect_optional optional_tree with
          | Some tt, Some None => Some None
          | Some tt, Some (Some index_tree) =>
              match phase1_surface_expect_sequence index_tree with
              | Some index_items =>
                  match phase1_surface_exact3 index_items with
                  | Some (open_tree, expression_tree, close_tree) =>
                      match phase1_surface_expect_literal "[" open_tree,
                            phase1_surface_expect_nonterminal
                              "expression" expression_tree,
                            phase1_surface_expect_literal "]" close_tree with
                      | Some tt, Some _, Some tt => Some (Some expression_tree)
                      | _, _, _ => None
                      end
                  | None => None
                  end
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_bytes_payload_round_trip :
  forall tree index_expression,
    phase1_surface_normalize_bytes_payload tree = Some index_expression ->
    phase1_surface_bytes_payload_tree index_expression = tree.
Proof.
  intros tree index_expression Hnormalize.
  unfold phase1_surface_normalize_bytes_payload in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[keyword_tree optional_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "Bytes" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_optional optional_tree)
    as [optional_value |] eqn:Hoptional; try discriminate Hnormalize.
  destruct optional_value as [index_tree |].
  - destruct (phase1_surface_expect_sequence index_tree)
      as [index_items |] eqn:Hindex_sequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact3 index_items)
      as [[[open_tree expression_tree] close_tree] |] eqn:Hindex_items;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "[" open_tree)
      as [[] |] eqn:Hopen; try discriminate Hnormalize.
    destruct
      (phase1_surface_expect_nonterminal "expression" expression_tree)
      as [expression_body |] eqn:Hexpression; try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "]" close_tree)
      as [[] |] eqn:Hclose; try discriminate Hnormalize.
    inversion Hnormalize; subst index_expression.
    unfold phase1_surface_bytes_payload_tree.
    rewrite (phase1_surface_expect_sequence_round_trip
      tree items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items keyword_tree optional_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip
      "Bytes" keyword_tree Hkeyword).
    rewrite (phase1_surface_expect_optional_round_trip
      optional_tree (Some index_tree) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip
      index_tree index_items Hindex_sequence).
    rewrite (phase1_surface_exact3_round_trip
      index_items open_tree expression_tree close_tree Hindex_items).
    rewrite (phase1_surface_expect_literal_round_trip
      "[" open_tree Hopen).
    rewrite (phase1_surface_expect_literal_round_trip
      "]" close_tree Hclose).
    reflexivity.
  - inversion Hnormalize; subst index_expression.
    unfold phase1_surface_bytes_payload_tree.
    rewrite (phase1_surface_expect_sequence_round_trip
      tree items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items keyword_tree optional_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip
      "Bytes" keyword_tree Hkeyword).
    rewrite (phase1_surface_expect_optional_round_trip
      optional_tree None Hoptional).
    reflexivity.
Qed.

Definition phase1_surface_bracketed_child_payload_tree
  (keyword : string)
  (child_tree : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral keyword;
      PTLiteral "[";
      child_tree;
      PTLiteral "]"
    ].

Definition phase1_surface_normalize_bracketed_child_payload
  (keyword child_name : string)
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact4 items with
      | Some (keyword_tree, open_tree, child_tree, close_tree) =>
          match phase1_surface_expect_literal keyword keyword_tree,
                phase1_surface_expect_literal "[" open_tree,
                phase1_surface_expect_nonterminal child_name child_tree,
                phase1_surface_expect_literal "]" close_tree with
          | Some tt, Some tt, Some _, Some tt => Some child_tree
          | _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_bracketed_child_payload_round_trip :
  forall keyword child_name tree child_tree,
    phase1_surface_normalize_bracketed_child_payload
      keyword child_name tree = Some child_tree ->
    phase1_surface_bracketed_child_payload_tree keyword child_tree = tree.
Proof.
  intros keyword child_name tree child_tree Hnormalize.
  unfold phase1_surface_normalize_bracketed_child_payload in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact4 items)
    as [[[[keyword_tree open_tree] actual_child_tree] close_tree] |]
      eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal keyword keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "[" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal child_name actual_child_tree)
    as [child_body |] eqn:Hchild; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "]" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst child_tree.
  unfold phase1_surface_bracketed_child_payload_tree.
  rewrite (phase1_surface_expect_sequence_round_trip
    tree items Hsequence).
  rewrite (phase1_surface_exact4_round_trip
    items keyword_tree open_tree actual_child_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    keyword keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip
    "[" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip
    "]" close_tree Hclose).
  reflexivity.
Qed.

Record Phase1SurfaceValidatedPayloadSpine : Type := {
  phase1_validated_payload_reference : ParseTree;
  phase1_validated_payload_first_expression : ParseTree;
  phase1_validated_payload_second_expression : ParseTree
}.

Definition phase1_surface_validated_payload_tree
  (payload : Phase1SurfaceValidatedPayloadSpine) : ParseTree :=
  PTSequence
    [ PTLiteral "Validated";
      PTLiteral "[";
      phase1_validated_payload_reference payload;
      PTLiteral ",";
      phase1_validated_payload_first_expression payload;
      PTLiteral ",";
      phase1_validated_payload_second_expression payload;
      PTLiteral "]"
    ].

Record Phase1SurfaceShallowExact8 : Type := {
  phase1_shallow_exact8_1 : ParseTree;
  phase1_shallow_exact8_2 : ParseTree;
  phase1_shallow_exact8_3 : ParseTree;
  phase1_shallow_exact8_4 : ParseTree;
  phase1_shallow_exact8_5 : ParseTree;
  phase1_shallow_exact8_6 : ParseTree;
  phase1_shallow_exact8_7 : ParseTree;
  phase1_shallow_exact8_8 : ParseTree
}.

Definition phase1_surface_shallow_exact8
  (items : list ParseTree) : option Phase1SurfaceShallowExact8 :=
  match items with
  | [a; b; c; d; e; f; g; h] =>
      Some
        {| phase1_shallow_exact8_1 := a;
           phase1_shallow_exact8_2 := b;
           phase1_shallow_exact8_3 := c;
           phase1_shallow_exact8_4 := d;
           phase1_shallow_exact8_5 := e;
           phase1_shallow_exact8_6 := f;
           phase1_shallow_exact8_7 := g;
           phase1_shallow_exact8_8 := h |}
  | _ => None
  end.

Lemma phase1_surface_shallow_exact8_round_trip :
  forall items exact,
    phase1_surface_shallow_exact8 items = Some exact ->
    items =
      [ phase1_shallow_exact8_1 exact;
        phase1_shallow_exact8_2 exact;
        phase1_shallow_exact8_3 exact;
        phase1_shallow_exact8_4 exact;
        phase1_shallow_exact8_5 exact;
        phase1_shallow_exact8_6 exact;
        phase1_shallow_exact8_7 exact;
        phase1_shallow_exact8_8 exact
      ].
Proof.
  intros items exact Hitems.
  destruct items as [|a items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|b items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|c items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|d items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|e items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|f items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|g items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|h items]; cbn in Hitems; try discriminate Hitems.
  destruct items as [|extra items]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst exact.
  reflexivity.
Qed.

Definition phase1_surface_normalize_validated_payload
  (tree : ParseTree) : option Phase1SurfaceValidatedPayloadSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_shallow_exact8 items with
      | Some exact =>
          match
            phase1_surface_expect_literal
              "Validated" (phase1_shallow_exact8_1 exact),
            phase1_surface_expect_literal
              "[" (phase1_shallow_exact8_2 exact),
            phase1_surface_expect_nonterminal
              "static_reference" (phase1_shallow_exact8_3 exact),
            phase1_surface_expect_literal
              "," (phase1_shallow_exact8_4 exact),
            phase1_surface_expect_nonterminal
              "expression" (phase1_shallow_exact8_5 exact),
            phase1_surface_expect_literal
              "," (phase1_shallow_exact8_6 exact),
            phase1_surface_expect_nonterminal
              "expression" (phase1_shallow_exact8_7 exact),
            phase1_surface_expect_literal
              "]" (phase1_shallow_exact8_8 exact)
          with
          | Some tt, Some tt, Some _, Some tt,
            Some _, Some tt, Some _, Some tt =>
              Some
                {| phase1_validated_payload_reference :=
                     phase1_shallow_exact8_3 exact;
                   phase1_validated_payload_first_expression :=
                     phase1_shallow_exact8_5 exact;
                   phase1_validated_payload_second_expression :=
                     phase1_shallow_exact8_7 exact |}
          | _, _, _, _, _, _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_validated_payload_round_trip :
  forall tree payload,
    phase1_surface_normalize_validated_payload tree = Some payload ->
    phase1_surface_validated_payload_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_validated_payload in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_shallow_exact8 items)
    as [exact |] eqn:Hexact; try discriminate Hnormalize.
  destruct exact as
    [keyword_tree open_tree reference_tree first_comma_tree
     first_expression_tree second_comma_tree second_expression_tree close_tree].
  cbn in Hnormalize, Hexact.
  destruct (phase1_surface_expect_literal "Validated" keyword_tree)
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "[" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal "static_reference" reference_tree)
    as [reference_body |] eqn:Hreference; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," first_comma_tree)
    as [[] |] eqn:Hfirst_comma; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal "expression" first_expression_tree)
    as [first_expression_body |] eqn:Hfirst_expression;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," second_comma_tree)
    as [[] |] eqn:Hsecond_comma; try discriminate Hnormalize.
  destruct (phase1_surface_expect_nonterminal "expression" second_expression_tree)
    as [second_expression_body |] eqn:Hsecond_expression;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "]" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst payload.
  unfold phase1_surface_validated_payload_tree.
  cbn.
  rewrite (phase1_surface_expect_sequence_round_trip
    tree items Hsequence).
  rewrite (phase1_surface_shallow_exact8_round_trip
    items
    {| phase1_shallow_exact8_1 := keyword_tree;
       phase1_shallow_exact8_2 := open_tree;
       phase1_shallow_exact8_3 := reference_tree;
       phase1_shallow_exact8_4 := first_comma_tree;
       phase1_shallow_exact8_5 := first_expression_tree;
       phase1_shallow_exact8_6 := second_comma_tree;
       phase1_shallow_exact8_7 := second_expression_tree;
       phase1_shallow_exact8_8 := close_tree |}
    Hexact).
  rewrite (phase1_surface_expect_literal_round_trip
    "Validated" keyword_tree Hkeyword).
  rewrite (phase1_surface_expect_literal_round_trip
    "[" open_tree Hopen).
  rewrite (phase1_surface_expect_literal_round_trip
    "," first_comma_tree Hfirst_comma).
  rewrite (phase1_surface_expect_literal_round_trip
    "," second_comma_tree Hsecond_comma).
  rewrite (phase1_surface_expect_literal_round_trip
    "]" close_tree Hclose).
  reflexivity.
Qed.

Inductive Phase1SurfaceShallowCompoundNonreferenceTypeSpine : Type :=
| Phase1ShallowPriorNonreferenceType
    (value : Phase1SurfacePrimitiveNonreferenceTypeSpine)
| Phase1ShallowBytesType
    (index_expression : option ParseTree)
| Phase1ShallowFrameType
    (reference_tree : ParseTree)
| Phase1ShallowProofType
    (proposition_tree : ParseTree)
| Phase1ShallowValidatedType
    (payload : Phase1SurfaceValidatedPayloadSpine)
| Phase1ShallowOpaqueNonreferenceType
    (tag : Phase1SurfaceNonreferenceTypeTag)
    (selected_tree : ParseTree).

Definition phase1_surface_shallow_compound_nonreference_type_spine_tree
  (type_value : Phase1SurfaceShallowCompoundNonreferenceTypeSpine) : ParseTree :=
  match type_value with
  | Phase1ShallowPriorNonreferenceType prior =>
      phase1_surface_primitive_nonreference_type_spine_tree prior
  | Phase1ShallowBytesType index_expression =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 7
          (phase1_surface_bytes_payload_tree index_expression))
  | Phase1ShallowFrameType reference_tree =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 8
          (phase1_surface_bracketed_child_payload_tree
            "Frame" reference_tree))
  | Phase1ShallowProofType proposition_tree =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 9
          (phase1_surface_bracketed_child_payload_tree
            "Proof" proposition_tree))
  | Phase1ShallowValidatedType payload =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 10
          (phase1_surface_validated_payload_tree payload))
  | Phase1ShallowOpaqueNonreferenceType tag selected_tree =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative
          (phase1_surface_nonreference_type_tag_index tag)
          selected_tree)
  end.

Definition phase1_surface_normalize_shallow_compound_nonreference_type_spine
  (type_value : Phase1SurfacePrimitiveNonreferenceTypeSpine)
  : option Phase1SurfaceShallowCompoundNonreferenceTypeSpine :=
  match type_value with
  | Phase1OpaqueNonreferenceType tag selected =>
      match tag with
      | Phase1BytesType =>
          match phase1_surface_normalize_bytes_payload selected with
          | Some index_expression => Some (Phase1ShallowBytesType index_expression)
          | None => None
          end
      | Phase1FrameType =>
          match phase1_surface_normalize_bracketed_child_payload
                  "Frame" "static_reference" selected with
          | Some reference_tree => Some (Phase1ShallowFrameType reference_tree)
          | None => None
          end
      | Phase1ProofType =>
          match phase1_surface_normalize_bracketed_child_payload
                  "Proof" "proposition" selected with
          | Some proposition_tree => Some (Phase1ShallowProofType proposition_tree)
          | None => None
          end
      | Phase1ValidatedType =>
          match phase1_surface_normalize_validated_payload selected with
          | Some payload => Some (Phase1ShallowValidatedType payload)
          | None => None
          end
      | _ => Some (Phase1ShallowOpaqueNonreferenceType tag selected)
      end
  | _ => Some (Phase1ShallowPriorNonreferenceType type_value)
  end.

Theorem phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_shallow_compound_nonreference_type_spine type_value =
      Some refined ->
    phase1_surface_shallow_compound_nonreference_type_spine_tree refined =
      phase1_surface_primitive_nonreference_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as
    [| | | |spelling |spelling |float_value |tag selected];
    cbn in Hnormalize.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - destruct tag; cbn in Hnormalize.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + destruct (phase1_surface_normalize_bytes_payload selected)
        as [index_expression |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_bytes_payload_round_trip
        selected index_expression Hselected).
      reflexivity.
    + destruct
        (phase1_surface_normalize_bracketed_child_payload
          "Frame" "static_reference" selected)
        as [reference_tree |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_bracketed_child_payload_round_trip
        "Frame" "static_reference" selected reference_tree Hselected).
      reflexivity.
    + destruct
        (phase1_surface_normalize_bracketed_child_payload
          "Proof" "proposition" selected)
        as [proposition_tree |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_bracketed_child_payload_round_trip
        "Proof" "proposition" selected proposition_tree Hselected).
      reflexivity.
    + destruct (phase1_surface_normalize_validated_payload selected)
        as [payload |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst refined.
      cbn.
      rewrite (phase1_surface_normalize_validated_payload_round_trip
        selected payload Hselected).
      reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
    + inversion Hnormalize; subst refined. reflexivity.
Qed.

Inductive Phase1SurfaceShallowCompoundTypeSpine : Type :=
| Phase1ShallowCompoundNonreferenceTypeSpine
    (type_value : Phase1SurfaceShallowCompoundNonreferenceTypeSpine)
| Phase1ShallowCompoundNamedTypeSpine
    (named_tree : ParseTree).

Definition phase1_surface_shallow_compound_type_spine_tree
  (type_value : Phase1SurfaceShallowCompoundTypeSpine) : ParseTree :=
  match type_value with
  | Phase1ShallowCompoundNonreferenceTypeSpine nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_shallow_compound_nonreference_type_spine_tree
            nonreference))
  | Phase1ShallowCompoundNamedTypeSpine named_tree =>
      PTNonterminal "type_expression"
        (PTAlternative 1 named_tree)
  end.

Definition phase1_surface_normalize_shallow_compound_type_spine
  (type_value : Phase1SurfacePrimitiveTypeSpine)
  : option Phase1SurfaceShallowCompoundTypeSpine :=
  match type_value with
  | Phase1PrimitiveNonreferenceTypeSpine nonreference =>
      match phase1_surface_normalize_shallow_compound_nonreference_type_spine
              nonreference with
      | Some refined =>
          Some (Phase1ShallowCompoundNonreferenceTypeSpine refined)
      | None => None
      end
  | Phase1PrimitiveNamedTypeSpine named_tree =>
      Some (Phase1ShallowCompoundNamedTypeSpine named_tree)
  end.

Theorem phase1_surface_normalize_shallow_compound_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_shallow_compound_type_spine type_value =
      Some refined ->
    phase1_surface_shallow_compound_type_spine_tree refined =
      phase1_surface_primitive_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as [nonreference | named_tree].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_shallow_compound_nonreference_type_spine
        nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_shallow_compound_type_tree
  (tree : ParseTree) : option Phase1SurfaceShallowCompoundTypeSpine :=
  match phase1_surface_normalize_primitive_type_tree tree with
  | Some type_value =>
      phase1_surface_normalize_shallow_compound_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_shallow_compound_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_shallow_compound_type_tree tree = Some refined ->
    phase1_surface_shallow_compound_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_shallow_compound_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_primitive_type_tree tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_primitive_type_spine_tree type_value).
  - eapply phase1_surface_normalize_shallow_compound_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_primitive_type_tree_round_trip.
    exact Htype.
Qed.
