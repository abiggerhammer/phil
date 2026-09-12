From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First recursive type-expression correspondence layer for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  The record/data declaration correspondence now reaches exact certified
  type_expression subtrees.  This layer normalizes the closed outer
  type_expression choice and the closed thirteen-way
  nonreference_type_expression choice while deliberately retaining each
  selected payload subtree for its own successor refinement.
*)

Inductive Phase1SurfaceNonreferenceTypeTag : Type :=
| Phase1UnitType
| Phase1BoolType
| Phase1CharType
| Phase1StringType
| Phase1UintType
| Phase1SintType
| Phase1FloatType
| Phase1BytesType
| Phase1FrameType
| Phase1ProofType
| Phase1ValidatedType
| Phase1RefinementType
| Phase1TupleType.

Definition phase1_surface_nonreference_type_tag_index
  (tag : Phase1SurfaceNonreferenceTypeTag) : nat :=
  match tag with
  | Phase1UnitType => 0
  | Phase1BoolType => 1
  | Phase1CharType => 2
  | Phase1StringType => 3
  | Phase1UintType => 4
  | Phase1SintType => 5
  | Phase1FloatType => 6
  | Phase1BytesType => 7
  | Phase1FrameType => 8
  | Phase1ProofType => 9
  | Phase1ValidatedType => 10
  | Phase1RefinementType => 11
  | Phase1TupleType => 12
  end.

Definition phase1_surface_nonreference_type_tag_of_index
  (index : nat) : option Phase1SurfaceNonreferenceTypeTag :=
  match index with
  | 0 => Some Phase1UnitType
  | 1 => Some Phase1BoolType
  | 2 => Some Phase1CharType
  | 3 => Some Phase1StringType
  | 4 => Some Phase1UintType
  | 5 => Some Phase1SintType
  | 6 => Some Phase1FloatType
  | 7 => Some Phase1BytesType
  | 8 => Some Phase1FrameType
  | 9 => Some Phase1ProofType
  | 10 => Some Phase1ValidatedType
  | 11 => Some Phase1RefinementType
  | 12 => Some Phase1TupleType
  | _ => None
  end.

Lemma phase1_surface_nonreference_type_tag_of_index_sound :
  forall index tag,
    phase1_surface_nonreference_type_tag_of_index index = Some tag ->
    index = phase1_surface_nonreference_type_tag_index tag.
Proof.
  intros index tag Htag.
  destruct index as [|index]; cbn in Htag.
  - inversion Htag; reflexivity.
  - destruct index as [|index]; cbn in Htag.
    + inversion Htag; reflexivity.
    + destruct index as [|index]; cbn in Htag.
      * inversion Htag; reflexivity.
      * destruct index as [|index]; cbn in Htag.
        -- inversion Htag; reflexivity.
        -- destruct index as [|index]; cbn in Htag.
           ++ inversion Htag; reflexivity.
           ++ destruct index as [|index]; cbn in Htag.
              ** inversion Htag; reflexivity.
              ** destruct index as [|index]; cbn in Htag.
                 --- inversion Htag; reflexivity.
                 --- destruct index as [|index]; cbn in Htag.
                     +++ inversion Htag; reflexivity.
                     +++ destruct index as [|index]; cbn in Htag.
                         *** inversion Htag; reflexivity.
                         *** destruct index as [|index]; cbn in Htag.
                             ---- inversion Htag; reflexivity.
                             ---- destruct index as [|index]; cbn in Htag.
                                  ++++ inversion Htag; reflexivity.
                                  ++++ destruct index as [|index]; cbn in Htag.
                                       ***** inversion Htag; reflexivity.
                                       ***** destruct index as [|index]; cbn in Htag.
                                             ------ inversion Htag; reflexivity.
                                             ------ discriminate Htag.
Qed.

Record Phase1SurfaceNonreferenceTypeSpine : Type := {
  phase1_nonreference_type_spine_tag : Phase1SurfaceNonreferenceTypeTag;
  phase1_nonreference_type_spine_selected_tree : ParseTree
}.

Definition phase1_surface_nonreference_type_spine_tree
  (type_value : Phase1SurfaceNonreferenceTypeSpine) : ParseTree :=
  PTNonterminal "nonreference_type_expression"
    (PTAlternative
      (phase1_surface_nonreference_type_tag_index
        (phase1_nonreference_type_spine_tag type_value))
      (phase1_nonreference_type_spine_selected_tree type_value)).

Definition phase1_surface_normalize_nonreference_type_spine
  (tree : ParseTree) : option Phase1SurfaceNonreferenceTypeSpine :=
  match phase1_surface_expect_nonterminal
          "nonreference_type_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_nonreference_type_tag_of_index index with
          | Some tag =>
              Some
                {| phase1_nonreference_type_spine_tag := tag;
                   phase1_nonreference_type_spine_selected_tree := selected |}
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_nonreference_type_spine_round_trip :
  forall tree type_value,
    phase1_surface_normalize_nonreference_type_spine tree = Some type_value ->
    phase1_surface_nonreference_type_spine_tree type_value = tree.
Proof.
  intros tree type_value Hnormalize.
  unfold phase1_surface_normalize_nonreference_type_spine in Hnormalize.
  destruct
    (phase1_surface_expect_nonterminal "nonreference_type_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_nonreference_type_tag_of_index index)
    as [tag |] eqn:Htag; try discriminate Hnormalize.
  inversion Hnormalize; subst type_value.
  unfold phase1_surface_nonreference_type_spine_tree.
  cbn.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "nonreference_type_expression" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite <- (phase1_surface_nonreference_type_tag_of_index_sound
    index tag Htag).
  reflexivity.
Qed.

Inductive Phase1SurfaceTypeSpine : Type :=
| Phase1NonreferenceTypeSpine
    (type_value : Phase1SurfaceNonreferenceTypeSpine)
| Phase1NamedTypeSpine
    (named_tree : ParseTree).

Definition phase1_surface_type_spine_tree
  (type_value : Phase1SurfaceTypeSpine) : ParseTree :=
  match type_value with
  | Phase1NonreferenceTypeSpine nonreference =>
      PTNonterminal "type_expression"
        (PTAlternative 0
          (phase1_surface_nonreference_type_spine_tree nonreference))
  | Phase1NamedTypeSpine named_tree =>
      PTNonterminal "type_expression"
        (PTAlternative 1 named_tree)
  end.

Definition phase1_surface_normalize_type_spine
  (tree : ParseTree) : option Phase1SurfaceTypeSpine :=
  match phase1_surface_expect_nonterminal "type_expression" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          match phase1_surface_normalize_nonreference_type_spine selected with
          | Some nonreference => Some (Phase1NonreferenceTypeSpine nonreference)
          | None => None
          end
      | Some (1, selected) => Some (Phase1NamedTypeSpine selected)
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_type_spine_round_trip :
  forall tree type_value,
    phase1_surface_normalize_type_spine tree = Some type_value ->
    phase1_surface_type_spine_tree type_value = tree.
Proof.
  intros tree type_value Hnormalize.
  unfold phase1_surface_normalize_type_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "type_expression" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_normalize_nonreference_type_spine selected)
      as [nonreference |] eqn:Hnonreference; try discriminate Hnormalize.
    inversion Hnormalize; subst type_value.
    unfold phase1_surface_type_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "type_expression" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite (phase1_surface_normalize_nonreference_type_spine_round_trip
      selected nonreference Hnonreference).
    reflexivity.
  - destruct index as [|index].
    + inversion Hnormalize; subst type_value.
      unfold phase1_surface_type_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "type_expression" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      reflexivity.
    + discriminate Hnormalize.
Qed.
