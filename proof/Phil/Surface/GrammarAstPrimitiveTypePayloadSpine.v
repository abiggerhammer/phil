From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTypeSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First payload refinement below the type-expression tag spine.

  The simple primitive alternatives are normalized completely here.  The
  recursive/compound alternatives remain exact selected ParseTree values for
  dedicated successor slices.
*)

Inductive Phase1SurfaceFloatPrimitive : Type :=
| Phase1Float32
| Phase1Float64.

Definition phase1_surface_float_primitive_tree
  (value : Phase1SurfaceFloatPrimitive) : ParseTree :=
  match value with
  | Phase1Float32 =>
      PTNonterminal "float_type"
        (PTAlternative 0 (PTLiteral "F32"))
  | Phase1Float64 =>
      PTNonterminal "float_type"
        (PTAlternative 1 (PTLiteral "F64"))
  end.

Definition phase1_surface_normalize_float_primitive
  (tree : ParseTree) : option Phase1SurfaceFloatPrimitive :=
  match phase1_surface_expect_nonterminal "float_type" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_expect_literal "F32" selected with
          | Some tt => Some Phase1Float32
          | None => None
          end
      | Some (1, selected) =>
          match phase1_surface_expect_literal "F64" selected with
          | Some tt => Some Phase1Float64
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_float_primitive_round_trip :
  forall tree value,
    phase1_surface_normalize_float_primitive tree = Some value ->
    phase1_surface_float_primitive_tree value = tree.
Proof.
  intros tree value Hnormalize.
  unfold phase1_surface_normalize_float_primitive in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "float_type" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_expect_literal "F32" selected)
      as [[] |] eqn:Hliteral; try discriminate Hnormalize.
    inversion Hnormalize; subst value.
    unfold phase1_surface_float_primitive_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "float_type" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite (phase1_surface_expect_literal_round_trip
      "F32" selected Hliteral).
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_expect_literal "F64" selected)
        as [[] |] eqn:Hliteral; try discriminate Hnormalize.
      inversion Hnormalize; subst value.
      unfold phase1_surface_float_primitive_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "float_type" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      rewrite (phase1_surface_expect_literal_round_trip
        "F64" selected Hliteral).
      reflexivity.
    + discriminate Hnormalize.
Qed.

Definition phase1_surface_normalize_lexical_type
  (name lexical_class : string)
  (tree : ParseTree) : option string :=
  match phase1_surface_expect_nonterminal name tree with
  | Some body => phase1_surface_expect_lexical lexical_class body
  | None => None
  end.

Theorem phase1_surface_normalize_lexical_type_round_trip :
  forall name lexical_class tree value,
    phase1_surface_normalize_lexical_type name lexical_class tree = Some value ->
    PTNonterminal name (PTLexical lexical_class value) = tree.
Proof.
  intros name lexical_class tree value Hnormalize.
  unfold phase1_surface_normalize_lexical_type in Hnormalize.
  destruct (phase1_surface_expect_nonterminal name tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_lexical lexical_class body)
    as [actual |] eqn:Hlex; try discriminate Hnormalize.
  inversion Hnormalize; subst value.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    name tree body Hnode).
  rewrite (phase1_surface_expect_lexical_round_trip
    lexical_class body actual Hlex).
  reflexivity.
Qed.

Inductive Phase1SurfacePrimitiveNonreferenceTypeSpine : Type :=
| Phase1PrimitiveUnitType
| Phase1PrimitiveBoolType
| Phase1PrimitiveCharType
| Phase1PrimitiveStringType
| Phase1PrimitiveUintType (spelling : string)
| Phase1PrimitiveSintType (spelling : string)
| Phase1PrimitiveFloatType (value : Phase1SurfaceFloatPrimitive)
| Phase1OpaqueNonreferenceType
    (tag : Phase1SurfaceNonreferenceTypeTag)
    (selected_tree : ParseTree).

Definition phase1_surface_primitive_nonreference_type_spine_tree
  (type_value : Phase1SurfacePrimitiveNonreferenceTypeSpine) : ParseTree :=
  match type_value with
  | Phase1PrimitiveUnitType =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 0 (PTLiteral "Unit"))
  | Phase1PrimitiveBoolType =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 1 (PTLiteral "Bool"))
  | Phase1PrimitiveCharType =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 2 (PTLiteral "Char"))
  | Phase1PrimitiveStringType =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 3 (PTLiteral "String"))
  | Phase1PrimitiveUintType spelling =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 4
          (PTNonterminal "uint_type" (PTLexical "UINT_TYPE" spelling)))
  | Phase1PrimitiveSintType spelling =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 5
          (PTNonterminal "sint_type" (PTLexical "SINT_TYPE" spelling)))
  | Phase1PrimitiveFloatType value =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative 6 (phase1_surface_float_primitive_tree value))
  | Phase1OpaqueNonreferenceType tag selected_tree =>
      PTNonterminal "nonreference_type_expression"
        (PTAlternative
          (phase1_surface_nonreference_type_tag_index tag)
          selected_tree)
  end.

Definition phase1_surface_normalize_primitive_nonreference_type_spine
  (type_value : Phase1SurfaceNonreferenceTypeSpine)
  : option Phase1SurfacePrimitiveNonreferenceTypeSpine :=
  let selected := phase1_nonreference_type_spine_selected_tree type_value in
  match phase1_nonreference_type_spine_tag type_value with
  | Phase1UnitType =>
      match phase1_surface_expect_literal "Unit" selected with
      | Some tt => Some Phase1PrimitiveUnitType
      | None => None
      end
  | Phase1BoolType =>
      match phase1_surface_expect_literal "Bool" selected with
      | Some tt => Some Phase1PrimitiveBoolType
      | None => None
      end
  | Phase1CharType =>
      match phase1_surface_expect_literal "Char" selected with
      | Some tt => Some Phase1PrimitiveCharType
      | None => None
      end
  | Phase1StringType =>
      match phase1_surface_expect_literal "String" selected with
      | Some tt => Some Phase1PrimitiveStringType
      | None => None
      end
  | Phase1UintType =>
      match phase1_surface_normalize_lexical_type
              "uint_type" "UINT_TYPE" selected with
      | Some spelling => Some (Phase1PrimitiveUintType spelling)
      | None => None
      end
  | Phase1SintType =>
      match phase1_surface_normalize_lexical_type
              "sint_type" "SINT_TYPE" selected with
      | Some spelling => Some (Phase1PrimitiveSintType spelling)
      | None => None
      end
  | Phase1FloatType =>
      match phase1_surface_normalize_float_primitive selected with
      | Some value => Some (Phase1PrimitiveFloatType value)
      | None => None
      end
  | Phase1BytesType =>
      Some (Phase1OpaqueNonreferenceType Phase1BytesType selected)
  | Phase1FrameType =>
      Some (Phase1OpaqueNonreferenceType Phase1FrameType selected)
  | Phase1ProofType =>
      Some (Phase1OpaqueNonreferenceType Phase1ProofType selected)
  | Phase1ValidatedType =>
      Some (Phase1OpaqueNonreferenceType Phase1ValidatedType selected)
  | Phase1RefinementType =>
      Some (Phase1OpaqueNonreferenceType Phase1RefinementType selected)
  | Phase1TupleType =>
      Some (Phase1OpaqueNonreferenceType Phase1TupleType selected)
  end.

Theorem phase1_surface_normalize_primitive_nonreference_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_primitive_nonreference_type_spine type_value =
      Some refined ->
    phase1_surface_primitive_nonreference_type_spine_tree refined =
      phase1_surface_nonreference_type_spine_tree type_value.
Proof.
  intros [tag selected] refined Hnormalize.
  destruct tag; cbn in Hnormalize.
  - destruct (phase1_surface_expect_literal "Unit" selected)
      as [[] |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_expect_literal_round_trip
      "Unit" selected Hselected).
    reflexivity.
  - destruct (phase1_surface_expect_literal "Bool" selected)
      as [[] |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_expect_literal_round_trip
      "Bool" selected Hselected).
    reflexivity.
  - destruct (phase1_surface_expect_literal "Char" selected)
      as [[] |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_expect_literal_round_trip
      "Char" selected Hselected).
    reflexivity.
  - destruct (phase1_surface_expect_literal "String" selected)
      as [[] |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_expect_literal_round_trip
      "String" selected Hselected).
    reflexivity.
  - destruct
      (phase1_surface_normalize_lexical_type
        "uint_type" "UINT_TYPE" selected)
      as [spelling |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_lexical_type_round_trip
      "uint_type" "UINT_TYPE" selected spelling Hselected).
    reflexivity.
  - destruct
      (phase1_surface_normalize_lexical_type
        "sint_type" "SINT_TYPE" selected)
      as [spelling |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_lexical_type_round_trip
      "sint_type" "SINT_TYPE" selected spelling Hselected).
    reflexivity.
  - destruct (phase1_surface_normalize_float_primitive selected)
      as [value |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite (phase1_surface_normalize_float_primitive_round_trip
      selected value Hselected).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Inductive Phase1SurfacePrimitiveTypeSpine : Type :=
| Phase1PrimitiveNonreferenceTypeSpine
    (type_value : Phase1SurfacePrimitiveNonreferenceTypeSpine)
| Phase1PrimitiveNamedTypeSpine
    (named_tree : ParseTree).

Definition phase1_surface_primitive_type_spine_tree
  (type_value : Phase1SurfacePrimitiveTypeSpine) : ParseTree :=
  match type_value with
  | Phase1PrimitiveNonreferenceTypeSpine nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_primitive_nonreference_type_spine_tree nonreference))
  | Phase1PrimitiveNamedTypeSpine named_tree =>
      PTNonterminal "type_expression"
        (PTAlternative 1 named_tree)
  end.

Definition phase1_surface_normalize_primitive_type_spine
  (type_value : Phase1SurfaceTypeSpine)
  : option Phase1SurfacePrimitiveTypeSpine :=
  match type_value with
  | Phase1NonreferenceTypeSpine nonreference =>
      match phase1_surface_normalize_primitive_nonreference_type_spine
              nonreference with
      | Some refined => Some (Phase1PrimitiveNonreferenceTypeSpine refined)
      | None => None
      end
  | Phase1NamedTypeSpine named_tree =>
      Some (Phase1PrimitiveNamedTypeSpine named_tree)
  end.

Theorem phase1_surface_normalize_primitive_type_spine_round_trip :
  forall type_value refined,
    phase1_surface_normalize_primitive_type_spine type_value = Some refined ->
    phase1_surface_primitive_type_spine_tree refined =
      phase1_surface_type_spine_tree type_value.
Proof.
  intros type_value refined Hnormalize.
  destruct type_value as [nonreference | named_tree].
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_primitive_nonreference_type_spine nonreference)
      as [actual |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_primitive_nonreference_type_spine_round_trip
        nonreference actual Hnonreference).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_primitive_type_tree
  (tree : ParseTree) : option Phase1SurfacePrimitiveTypeSpine :=
  match phase1_surface_normalize_type_spine tree with
  | Some type_value => phase1_surface_normalize_primitive_type_spine type_value
  | None => None
  end.

Theorem phase1_surface_normalize_primitive_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_primitive_type_tree tree = Some refined ->
    phase1_surface_primitive_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_primitive_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_type_spine tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  transitivity (phase1_surface_type_spine_tree type_value).
  - eapply phase1_surface_normalize_primitive_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_type_spine_round_trip.
    exact Htype.
Qed.
