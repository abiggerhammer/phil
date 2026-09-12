From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Shared structural-mode correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  Generic-parameter refinement leaves the optional record mode clause as a
  certified ParseTree.  This layer normalizes the closed three-way
  structural_mode choice and the enclosing optional "mode" clause, then
  refines the record carrier to hold that normalized value.
*)

Inductive Phase1SurfaceStructuralMode : Type :=
| Phase1UnrestrictedMode
| Phase1AffineMode
| Phase1LinearMode.

Definition phase1_surface_structural_mode_index
  (mode : Phase1SurfaceStructuralMode) : nat :=
  match mode with
  | Phase1UnrestrictedMode => 0
  | Phase1AffineMode => 1
  | Phase1LinearMode => 2
  end.

Definition phase1_surface_structural_mode_of_index
  (index : nat) : option Phase1SurfaceStructuralMode :=
  match index with
  | 0 => Some Phase1UnrestrictedMode
  | 1 => Some Phase1AffineMode
  | 2 => Some Phase1LinearMode
  | _ => None
  end.

Definition phase1_surface_structural_mode_literal
  (mode : Phase1SurfaceStructuralMode) : string :=
  match mode with
  | Phase1UnrestrictedMode => "unrestricted"
  | Phase1AffineMode => "affine"
  | Phase1LinearMode => "linear"
  end.

Lemma phase1_surface_structural_mode_index_round_trip :
  forall index mode,
    phase1_surface_structural_mode_of_index index = Some mode ->
    phase1_surface_structural_mode_index mode = index.
Proof.
  intros index mode Hmode.
  destruct index as [|index]; cbn in Hmode.
  - inversion Hmode; reflexivity.
  - destruct index as [|index]; cbn in Hmode.
    + inversion Hmode; reflexivity.
    + destruct index as [|index]; cbn in Hmode.
      * inversion Hmode; reflexivity.
      * discriminate Hmode.
Qed.

Definition phase1_surface_structural_mode_tree
  (mode : Phase1SurfaceStructuralMode) : ParseTree :=
  PTNonterminal "structural_mode"
    (PTAlternative
      (phase1_surface_structural_mode_index mode)
      (PTLiteral (phase1_surface_structural_mode_literal mode))).

Definition phase1_surface_normalize_structural_mode
  (tree : ParseTree) : option Phase1SurfaceStructuralMode :=
  match phase1_surface_expect_nonterminal "structural_mode" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (index, selected) =>
          match phase1_surface_structural_mode_of_index index with
          | Some mode =>
              match phase1_surface_expect_literal
                      (phase1_surface_structural_mode_literal mode) selected with
              | Some tt => Some mode
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_structural_mode_round_trip :
  forall tree mode,
    phase1_surface_normalize_structural_mode tree = Some mode ->
    phase1_surface_structural_mode_tree mode = tree.
Proof.
  intros tree mode Hnormalize.
  unfold phase1_surface_normalize_structural_mode in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "structural_mode" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct (phase1_surface_structural_mode_of_index index)
    as [actual |] eqn:Hmode; try discriminate Hnormalize.
  destruct
    (phase1_surface_expect_literal
      (phase1_surface_structural_mode_literal actual) selected)
    as [[] |] eqn:Hselected; try discriminate Hnormalize.
  inversion Hnormalize; subst mode.
  unfold phase1_surface_structural_mode_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "structural_mode" tree body Hnode).
  rewrite (phase1_surface_expect_alternative_round_trip
    body index selected Halternative).
  rewrite (phase1_surface_structural_mode_index_round_trip index actual Hmode).
  rewrite (phase1_surface_expect_literal_round_trip
    (phase1_surface_structural_mode_literal actual) selected Hselected).
  reflexivity.
Qed.

Definition phase1_surface_optional_mode_tree
  (mode : option Phase1SurfaceStructuralMode) : ParseTree :=
  match mode with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (PTSequence
          [ PTLiteral "mode";
            phase1_surface_structural_mode_tree value
          ])
  end.

Definition phase1_surface_normalize_optional_mode
  (tree : ParseTree) : option (option Phase1SurfaceStructuralMode) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (keyword_tree, mode_tree) =>
              match phase1_surface_expect_literal "mode" keyword_tree,
                    phase1_surface_normalize_structural_mode mode_tree with
              | Some tt, Some mode => Some (Some mode)
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_mode_round_trip :
  forall tree mode,
    phase1_surface_normalize_optional_mode tree = Some mode ->
    phase1_surface_optional_mode_tree mode = tree.
Proof.
  intros tree mode Hnormalize.
  unfold phase1_surface_normalize_optional_mode in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_expect_sequence body)
      as [items |] eqn:Hsequence; try discriminate Hnormalize.
    destruct (phase1_surface_exact2 items)
      as [[keyword_tree mode_tree] |] eqn:Hitems;
      try discriminate Hnormalize.
    destruct (phase1_surface_expect_literal "mode" keyword_tree)
      as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_structural_mode mode_tree)
      as [actual |] eqn:Hmode; try discriminate Hnormalize.
    inversion Hnormalize; subst mode.
    unfold phase1_surface_optional_mode_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
    rewrite (phase1_surface_exact2_round_trip
      items keyword_tree mode_tree Hitems).
    rewrite (phase1_surface_expect_literal_round_trip
      "mode" keyword_tree Hkeyword).
    rewrite (phase1_surface_normalize_structural_mode_round_trip
      mode_tree actual Hmode).
    reflexivity.
  - inversion Hnormalize; subst mode.
    unfold phase1_surface_optional_mode_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceRecordModeSpine : Type := {
  phase1_record_mode_spine_name : string;
  phase1_record_mode_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_record_mode_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_record_mode_spine_requirements_tree : ParseTree;
  phase1_record_mode_spine_fields_tree : ParseTree
}.

Definition phase1_surface_record_mode_spine_tree
  (record : Phase1SurfaceRecordModeSpine) : ParseTree :=
  PTNonterminal "record_decl"
    (PTSequence
      [ PTLiteral "record";
        phase1_surface_identifier_tree
          (phase1_record_mode_spine_name record);
        phase1_surface_optional_generic_params_tree
          (phase1_record_mode_spine_generic_params record);
        phase1_surface_optional_mode_tree
          (phase1_record_mode_spine_mode record);
        phase1_record_mode_spine_requirements_tree record;
        PTLiteral "{";
        phase1_record_mode_spine_fields_tree record;
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_record_mode_spine
  (record : Phase1SurfaceRecordGenericSpine)
  : option Phase1SurfaceRecordModeSpine :=
  match phase1_surface_normalize_optional_mode
          (phase1_record_generic_spine_mode_tree record) with
  | Some mode =>
      Some
        {| phase1_record_mode_spine_name :=
             phase1_record_generic_spine_name record;
           phase1_record_mode_spine_generic_params :=
             phase1_record_generic_spine_generic_params record;
           phase1_record_mode_spine_mode := mode;
           phase1_record_mode_spine_requirements_tree :=
             phase1_record_generic_spine_requirements_tree record;
           phase1_record_mode_spine_fields_tree :=
             phase1_record_generic_spine_fields_tree record |}
  | None => None
  end.

Theorem phase1_surface_normalize_record_mode_spine_round_trip :
  forall record refined,
    phase1_surface_normalize_record_mode_spine record = Some refined ->
    phase1_surface_record_mode_spine_tree refined =
      phase1_surface_record_generic_spine_tree record.
Proof.
  intros [name generic_params mode_tree requirements_tree fields_tree]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_optional_mode mode_tree)
    as [mode |] eqn:Hmode; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_record_mode_spine_tree,
    phase1_surface_record_generic_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_optional_mode_round_trip
    mode_tree mode Hmode).
  reflexivity.
Qed.

Definition phase1_surface_normalize_record_mode_tree
  (tree : ParseTree) : option Phase1SurfaceRecordModeSpine :=
  match phase1_surface_normalize_record_generic_tree tree with
  | Some record => phase1_surface_normalize_record_mode_spine record
  | None => None
  end.

Theorem phase1_surface_normalize_record_mode_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_record_mode_tree tree = Some refined ->
    phase1_surface_record_mode_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_record_mode_tree in Hnormalize.
  destruct (phase1_surface_normalize_record_generic_tree tree)
    as [record |] eqn:Hrecord; try discriminate Hnormalize.
  transitivity (phase1_surface_record_generic_spine_tree record).
  - eapply phase1_surface_normalize_record_mode_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_record_generic_tree_round_trip.
    exact Hrecord.
Qed.
