From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstDataSpine
  GrammarAstGenericRequirementsSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Variant-declaration correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarAstDataSpine normalizes the outer data_decl structure while retaining
  each variant_decl as an exact certified ParseTree.  This layer descends one
  step: it normalizes each variant name and the optional variant_payload slot,
  while deliberately retaining the variant_payload subtree itself for the next
  recursive correspondence slice.
*)

Definition phase1_surface_optional_variant_payload_tree
  (payload : option ParseTree) : ParseTree :=
  match payload with
  | None => PTOptionalNone
  | Some tree => PTOptionalSome tree
  end.

Definition phase1_surface_normalize_optional_variant_payload
  (tree : ParseTree) : option (option ParseTree) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some payload) =>
      match phase1_surface_validate_named_node "variant_payload" payload with
      | Some tt => Some (Some payload)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_variant_payload_round_trip :
  forall tree payload,
    phase1_surface_normalize_optional_variant_payload tree = Some payload ->
    phase1_surface_optional_variant_payload_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_optional_variant_payload in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[payload_tree |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_validate_named_node "variant_payload" payload_tree)
      as [[] |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst payload.
    unfold phase1_surface_optional_variant_payload_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some payload_tree) Hoptional).
    reflexivity.
  - inversion Hnormalize; subst payload.
    unfold phase1_surface_optional_variant_payload_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceVariantSpine : Type := {
  phase1_variant_spine_name : string;
  phase1_variant_spine_payload : option ParseTree
}.

Definition phase1_surface_variant_spine_tree
  (variant : Phase1SurfaceVariantSpine) : ParseTree :=
  PTNonterminal "variant_decl"
    (PTSequence
      [ phase1_surface_identifier_tree (phase1_variant_spine_name variant);
        phase1_surface_optional_variant_payload_tree
          (phase1_variant_spine_payload variant)
      ]).

Definition phase1_surface_normalize_variant_spine
  (tree : ParseTree) : option Phase1SurfaceVariantSpine :=
  match phase1_surface_expect_nonterminal "variant_decl" tree with
  | Some body =>
      match phase1_surface_expect_sequence body with
      | Some items =>
          match phase1_surface_exact2 items with
          | Some (name_tree, payload_tree) =>
              match phase1_surface_normalize_identifier name_tree,
                    phase1_surface_normalize_optional_variant_payload payload_tree with
              | Some name, Some payload =>
                  Some
                    {| phase1_variant_spine_name := name;
                       phase1_variant_spine_payload := payload |}
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_variant_spine_round_trip :
  forall tree variant,
    phase1_surface_normalize_variant_spine tree = Some variant ->
    phase1_surface_variant_spine_tree variant = tree.
Proof.
  intros tree variant Hnormalize.
  unfold phase1_surface_normalize_variant_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "variant_decl" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_sequence body)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[name_tree payload_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_identifier name_tree)
    as [name |] eqn:Hname; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_optional_variant_payload payload_tree)
    as [payload |] eqn:Hpayload; try discriminate Hnormalize.
  inversion Hnormalize; subst variant.
  unfold phase1_surface_variant_spine_tree.
  rewrite (phase1_surface_expect_nonterminal_round_trip
    "variant_decl" tree body Hnode).
  rewrite (phase1_surface_expect_sequence_round_trip body items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items name_tree payload_tree Hitems).
  rewrite (phase1_surface_normalize_identifier_round_trip
    name_tree name Hname).
  rewrite (phase1_surface_normalize_optional_variant_payload_round_trip
    payload_tree payload Hpayload).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_variant_spines
  (trees : list ParseTree) : option (list Phase1SurfaceVariantSpine) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_variant_spine tree,
            phase1_surface_normalize_variant_spines rest with
      | Some variant, Some variants => Some (variant :: variants)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_variant_spines_round_trip :
  forall trees variants,
    phase1_surface_normalize_variant_spines trees = Some variants ->
    map phase1_surface_variant_spine_tree variants = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros variants Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst variants.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_variant_spine tree)
      as [variant |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_variant_spines rest)
      as [rest_variants |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst variants.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_variant_spine_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_refined_data_variant_suffix_tree
  (variant : Phase1SurfaceVariantSpine) : ParseTree :=
  phase1_surface_data_variant_suffix_tree
    (phase1_surface_variant_spine_tree variant).

Lemma phase1_surface_normalize_variant_spines_suffix_round_trip :
  forall trees variants,
    phase1_surface_normalize_variant_spines trees = Some variants ->
    map phase1_surface_refined_data_variant_suffix_tree variants =
      map phase1_surface_data_variant_suffix_tree trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros variants Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst variants.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_variant_spine tree)
      as [variant |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_variant_spines rest)
      as [rest_variants |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst variants.
    cbn.
    f_equal.
    - unfold phase1_surface_refined_data_variant_suffix_tree.
      rewrite (phase1_surface_normalize_variant_spine_round_trip
        tree variant Htree).
      reflexivity.
    - eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceDataVariantSpine : Type := {
  phase1_data_variant_spine_name : string;
  phase1_data_variant_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_data_variant_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_data_variant_spine_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_data_variant_spine_first_variant : Phase1SurfaceVariantSpine;
  phase1_data_variant_spine_rest_variants : list Phase1SurfaceVariantSpine
}.

Definition phase1_surface_data_variant_spine_tree
  (data_value : Phase1SurfaceDataVariantSpine) : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree (phase1_data_variant_spine_name data_value);
        phase1_surface_optional_generic_params_tree
          (phase1_data_variant_spine_generic_params data_value);
        phase1_surface_optional_mode_tree
          (phase1_data_variant_spine_mode data_value);
        phase1_surface_optional_generic_requirements_tree
          (phase1_data_variant_spine_requirements data_value);
        PTLiteral "=";
        phase1_surface_variant_spine_tree
          (phase1_data_variant_spine_first_variant data_value);
        PTRepetition
          (map phase1_surface_refined_data_variant_suffix_tree
            (phase1_data_variant_spine_rest_variants data_value));
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_data_variant_spine
  (data_value : Phase1SurfaceDataSpine)
  : option Phase1SurfaceDataVariantSpine :=
  match phase1_surface_normalize_variant_spine
          (phase1_data_spine_first_variant_tree data_value),
        phase1_surface_normalize_variant_spines
          (phase1_data_spine_rest_variant_trees data_value) with
  | Some first_variant, Some rest_variants =>
      Some
        {| phase1_data_variant_spine_name := phase1_data_spine_name data_value;
           phase1_data_variant_spine_generic_params :=
             phase1_data_spine_generic_params data_value;
           phase1_data_variant_spine_mode := phase1_data_spine_mode data_value;
           phase1_data_variant_spine_requirements :=
             phase1_data_spine_requirements data_value;
           phase1_data_variant_spine_first_variant := first_variant;
           phase1_data_variant_spine_rest_variants := rest_variants |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_data_variant_spine_round_trip :
  forall data_value refined,
    phase1_surface_normalize_data_variant_spine data_value = Some refined ->
    phase1_surface_data_variant_spine_tree refined =
      phase1_surface_data_spine_tree data_value.
Proof.
  intros
    [name generic_params mode requirements first_variant_tree rest_variant_trees]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_variant_spine first_variant_tree)
    as [first_variant |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_variant_spines rest_variant_trees)
    as [rest_variants |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_data_variant_spine_tree,
    phase1_surface_data_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_variant_spine_round_trip
    first_variant_tree first_variant Hfirst).
  rewrite (phase1_surface_normalize_variant_spines_suffix_round_trip
    rest_variant_trees rest_variants Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_data_variant_tree
  (tree : ParseTree) : option Phase1SurfaceDataVariantSpine :=
  match phase1_surface_normalize_data_spine tree with
  | Some data_value => phase1_surface_normalize_data_variant_spine data_value
  | None => None
  end.

Theorem phase1_surface_normalize_data_variant_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_data_variant_tree tree = Some refined ->
    phase1_surface_data_variant_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_data_variant_tree in Hnormalize.
  destruct (phase1_surface_normalize_data_spine tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  transitivity (phase1_surface_data_spine_tree data_value).
  - eapply phase1_surface_normalize_data_variant_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_data_spine_round_trip.
    exact Hdata.
Qed.
