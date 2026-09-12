From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordFieldsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  First data-declaration correspondence layer for
  PHIL-SURFACE-GRAMMAR-CORR-001.

  Record correspondence has established reusable normalization for identifiers,
  generic parameters, structural mode, generic requirements, and field lists.
  This layer reuses the shared declaration payloads for data_decl and normalizes
  the ordered variant spine while retaining each variant_decl itself as an exact
  certified ParseTree for its dedicated successor refinement.
*)

Record Phase1SurfaceExact9 (A : Type) : Type := {
  phase1_exact9_1 : A;
  phase1_exact9_2 : A;
  phase1_exact9_3 : A;
  phase1_exact9_4 : A;
  phase1_exact9_5 : A;
  phase1_exact9_6 : A;
  phase1_exact9_7 : A;
  phase1_exact9_8 : A;
  phase1_exact9_9 : A
}.

Definition phase1_surface_exact9 {A : Type}
  (items : list A) : option (Phase1SurfaceExact9 A) :=
  match items with
  | [a; b; c; d; e; f; g; h; i] =>
      Some
        {| phase1_exact9_1 := a;
           phase1_exact9_2 := b;
           phase1_exact9_3 := c;
           phase1_exact9_4 := d;
           phase1_exact9_5 := e;
           phase1_exact9_6 := f;
           phase1_exact9_7 := g;
           phase1_exact9_8 := h;
           phase1_exact9_9 := i |}
  | _ => None
  end.

Lemma phase1_surface_exact9_round_trip {A : Type} :
  forall (items : list A) (fields : Phase1SurfaceExact9 A),
    phase1_surface_exact9 items = Some fields ->
    items =
      [ phase1_exact9_1 fields;
        phase1_exact9_2 fields;
        phase1_exact9_3 fields;
        phase1_exact9_4 fields;
        phase1_exact9_5 fields;
        phase1_exact9_6 fields;
        phase1_exact9_7 fields;
        phase1_exact9_8 fields;
        phase1_exact9_9 fields
      ].
Proof.
  intros items fields Hitems.
  destruct items as [|a rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|b rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|c rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|d rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|e rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|f rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|g rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|h rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|i rest]; cbn in Hitems; try discriminate Hitems.
  destruct rest as [|extra rest]; cbn in Hitems; try discriminate Hitems.
  inversion Hitems; subst.
  reflexivity.
Qed.

Definition phase1_surface_data_variant_suffix_tree
  (variant_tree : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral "|";
      variant_tree
    ].

Definition phase1_surface_normalize_data_variant_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (bar_tree, variant_tree) =>
          match phase1_surface_expect_literal "|" bar_tree,
                phase1_surface_validate_named_node "variant_decl" variant_tree with
          | Some tt, Some tt => Some variant_tree
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_data_variant_suffix_round_trip :
  forall tree variant_tree,
    phase1_surface_normalize_data_variant_suffix tree = Some variant_tree ->
    phase1_surface_data_variant_suffix_tree variant_tree = tree.
Proof.
  intros tree variant_tree Hnormalize.
  unfold phase1_surface_normalize_data_variant_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[bar_tree selected_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "|" bar_tree)
    as [[] |] eqn:Hbar; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "variant_decl" selected_tree)
    as [[] |] eqn:Hvariant; try discriminate Hnormalize.
  inversion Hnormalize; subst variant_tree.
  unfold phase1_surface_data_variant_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items bar_tree selected_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "|" bar_tree Hbar).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_data_variant_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_data_variant_suffix tree,
            phase1_surface_normalize_data_variant_suffixes rest with
      | Some variant_tree, Some variants => Some (variant_tree :: variants)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_data_variant_suffixes_round_trip :
  forall trees variants,
    phase1_surface_normalize_data_variant_suffixes trees = Some variants ->
    map phase1_surface_data_variant_suffix_tree variants = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros variants Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst variants.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_data_variant_suffix tree)
      as [variant_tree |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_data_variant_suffixes rest)
      as [rest_variants |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst variants.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_data_variant_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceDataSpine : Type := {
  phase1_data_spine_name : string;
  phase1_data_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_data_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_data_spine_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_data_spine_first_variant_tree : ParseTree;
  phase1_data_spine_rest_variant_trees : list ParseTree
}.

Definition phase1_surface_data_spine_tree
  (data : Phase1SurfaceDataSpine) : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree (phase1_data_spine_name data);
        phase1_surface_optional_generic_params_tree
          (phase1_data_spine_generic_params data);
        phase1_surface_optional_mode_tree
          (phase1_data_spine_mode data);
        phase1_surface_optional_generic_requirements_tree
          (phase1_data_spine_requirements data);
        PTLiteral "=";
        phase1_data_spine_first_variant_tree data;
        PTRepetition
          (map phase1_surface_data_variant_suffix_tree
            (phase1_data_spine_rest_variant_trees data));
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_data_spine
  (tree : ParseTree) : option Phase1SurfaceDataSpine :=
  match phase1_surface_expect_nonterminal "data_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact9 items with
          | Some fields =>
              let keyword_tree := phase1_exact9_1 fields in
              let name_tree := phase1_exact9_2 fields in
              let generic_tree := phase1_exact9_3 fields in
              let mode_tree := phase1_exact9_4 fields in
              let requirements_tree := phase1_exact9_5 fields in
              let equals_tree := phase1_exact9_6 fields in
              let first_variant_tree := phase1_exact9_7 fields in
              let rest_tree := phase1_exact9_8 fields in
              let terminator_tree := phase1_exact9_9 fields in
              match phase1_surface_expect_literal "data" keyword_tree,
                    phase1_surface_expect_literal "=" equals_tree,
                    phase1_surface_validate_named_node
                      "variant_decl" first_variant_tree,
                    phase1_surface_expect_repetition rest_tree,
                    phase1_surface_expect_literal ";" terminator_tree with
              | Some tt, Some tt, Some tt, Some rest_trees, Some tt =>
                  match phase1_surface_normalize_identifier name_tree,
                        phase1_surface_normalize_optional_generic_params generic_tree,
                        phase1_surface_normalize_optional_mode mode_tree,
                        phase1_surface_normalize_optional_generic_requirements
                          requirements_tree,
                        phase1_surface_normalize_data_variant_suffixes rest_trees with
                  | Some name, Some generic_params, Some mode,
                    Some requirements, Some rest_variants =>
                      Some
                        {| phase1_data_spine_name := name;
                           phase1_data_spine_generic_params := generic_params;
                           phase1_data_spine_mode := mode;
                           phase1_data_spine_requirements := requirements;
                           phase1_data_spine_first_variant_tree := first_variant_tree;
                           phase1_data_spine_rest_variant_trees := rest_variants |}
                  | _, _, _, _, _ => None
                  end
              | _, _, _, _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_data_spine_round_trip :
  forall tree data,
    phase1_surface_normalize_data_spine tree = Some data ->
    phase1_surface_data_spine_tree data = tree.
Proof.
  intros tree data Hnormalize.
  unfold phase1_surface_normalize_data_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "data_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact9 items)
    as [fields |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "data" (phase1_exact9_1 fields))
    as [[] |] eqn:Hkeyword; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "=" (phase1_exact9_6 fields))
    as [[] |] eqn:Hequals; try discriminate Hnormalize.
  destruct
    (phase1_surface_validate_named_node
      "variant_decl" (phase1_exact9_7 fields))
    as [[] |] eqn:Hfirst_variant; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition (phase1_exact9_8 fields))
    as [rest_trees |] eqn:Hrest_trees; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ";" (phase1_exact9_9 fields))
    as [[] |] eqn:Hterminator; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier (phase1_exact9_2 fields))
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_params (phase1_exact9_3 fields))
    as [generic_params |] eqn:Hgeneric; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_optional_mode (phase1_exact9_4 fields))
    as [mode |] eqn:Hmode; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements
      (phase1_exact9_5 fields))
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_data_variant_suffixes rest_trees)
    as [rest_variants |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst data.
  unfold phase1_surface_data_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "data_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact9_round_trip items fields Hitems).
  rewrite (phase1_surface_expect_literal_round_trip
    "data" (phase1_exact9_1 fields) Hkeyword).
  rewrite (phase1_surface_normalize_identifier_round_trip
    (phase1_exact9_2 fields) name Hname).
  rewrite (phase1_surface_normalize_optional_generic_params_round_trip
    (phase1_exact9_3 fields) generic_params Hgeneric).
  rewrite (phase1_surface_normalize_optional_mode_round_trip
    (phase1_exact9_4 fields) mode Hmode).
  rewrite (phase1_surface_normalize_optional_generic_requirements_round_trip
    (phase1_exact9_5 fields) requirements Hrequirements).
  rewrite (phase1_surface_expect_literal_round_trip
    "=" (phase1_exact9_6 fields) Hequals).
  rewrite (phase1_surface_expect_repetition_round_trip
    (phase1_exact9_8 fields) rest_trees Hrest_trees).
  rewrite (phase1_surface_normalize_data_variant_suffixes_round_trip
    rest_trees rest_variants Hrest).
  rewrite (phase1_surface_expect_literal_round_trip
    ";" (phase1_exact9_9 fields) Hterminator).
  reflexivity.
Qed.
