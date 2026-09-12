From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstVariantSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Variant-payload correspondence for PHIL-SURFACE-GRAMMAR-CORR-001.

  GrammarAstVariantSpine normalizes variant names while retaining any
  variant_payload subtree exactly.  This layer normalizes the two payload
  alternatives.  Record-shaped payloads reuse the field-list spine established
  for record declarations.  Tuple payloads normalize their optional nonempty
  comma-separated type_expression list while retaining each type-expression
  subtree exactly for the dedicated type correspondence layer.
*)

Definition phase1_surface_tuple_type_suffix_tree
  (type_tree : ParseTree) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      type_tree
    ].

Definition phase1_surface_normalize_tuple_type_suffix
  (tree : ParseTree) : option ParseTree :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (comma_tree, type_tree) =>
          match phase1_surface_expect_literal "," comma_tree,
                phase1_surface_validate_named_node "type_expression" type_tree with
          | Some tt, Some tt => Some type_tree
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_type_suffix_round_trip :
  forall tree type_tree,
    phase1_surface_normalize_tuple_type_suffix tree = Some type_tree ->
    phase1_surface_tuple_type_suffix_tree type_tree = tree.
Proof.
  intros tree type_tree Hnormalize.
  unfold phase1_surface_normalize_tuple_type_suffix in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[comma_tree actual_type_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "," comma_tree)
    as [[] |] eqn:Hcomma; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "type_expression" actual_type_tree)
    as [[] |] eqn:Htype; try discriminate Hnormalize.
  inversion Hnormalize; subst type_tree.
  unfold phase1_surface_tuple_type_suffix_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip
    items comma_tree actual_type_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "," comma_tree Hcomma).
  reflexivity.
Qed.

Fixpoint phase1_surface_normalize_tuple_type_suffixes
  (trees : list ParseTree) : option (list ParseTree) :=
  match trees with
  | [] => Some []
  | tree :: rest =>
      match phase1_surface_normalize_tuple_type_suffix tree,
            phase1_surface_normalize_tuple_type_suffixes rest with
      | Some type_tree, Some types => Some (type_tree :: types)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_tuple_type_suffixes_round_trip :
  forall trees types,
    phase1_surface_normalize_tuple_type_suffixes trees = Some types ->
    map phase1_surface_tuple_type_suffix_tree types = trees.
Proof.
  intros trees.
  induction trees as [|tree rest IH]; intros types Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst types.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_tuple_type_suffix tree)
      as [type_tree |] eqn:Htree; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_tuple_type_suffixes rest)
      as [rest_types |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst types.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_tuple_type_suffix_round_trip.
      exact Htree.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceTupleTypeListSpine : Type := {
  phase1_tuple_type_list_spine_first : ParseTree;
  phase1_tuple_type_list_spine_rest : list ParseTree
}.

Definition phase1_surface_tuple_type_list_spine_tree
  (types : Phase1SurfaceTupleTypeListSpine) : ParseTree :=
  PTSequence
    [ phase1_tuple_type_list_spine_first types;
      PTRepetition
        (map phase1_surface_tuple_type_suffix_tree
          (phase1_tuple_type_list_spine_rest types))
    ].

Definition phase1_surface_normalize_tuple_type_list_spine
  (tree : ParseTree) : option Phase1SurfaceTupleTypeListSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact2 items with
      | Some (first_tree, rest_tree) =>
          match phase1_surface_validate_named_node "type_expression" first_tree,
                phase1_surface_expect_repetition rest_tree with
          | Some tt, Some rest_trees =>
              match phase1_surface_normalize_tuple_type_suffixes rest_trees with
              | Some rest =>
                  Some
                    {| phase1_tuple_type_list_spine_first := first_tree;
                       phase1_tuple_type_list_spine_rest := rest |}
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_type_list_spine_round_trip :
  forall tree types,
    phase1_surface_normalize_tuple_type_list_spine tree = Some types ->
    phase1_surface_tuple_type_list_spine_tree types = tree.
Proof.
  intros tree types Hnormalize.
  unfold phase1_surface_normalize_tuple_type_list_spine in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact2 items)
    as [[first_tree rest_tree] |] eqn:Hitems; try discriminate Hnormalize.
  destruct (phase1_surface_validate_named_node "type_expression" first_tree)
    as [[] |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_expect_repetition rest_tree)
    as [rest_trees |] eqn:Hrest_trees; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_tuple_type_suffixes rest_trees)
    as [rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst types.
  unfold phase1_surface_tuple_type_list_spine_tree.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact2_round_trip items first_tree rest_tree Hitems).
  rewrite (phase1_surface_expect_repetition_round_trip
    rest_tree rest_trees Hrest_trees).
  rewrite (phase1_surface_normalize_tuple_type_suffixes_round_trip
    rest_trees rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_optional_tuple_types_tree
  (types : option Phase1SurfaceTupleTypeListSpine) : ParseTree :=
  match types with
  | None => PTOptionalNone
  | Some value => PTOptionalSome (phase1_surface_tuple_type_list_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_tuple_types
  (tree : ParseTree) : option (option Phase1SurfaceTupleTypeListSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_tuple_type_list_spine body with
      | Some types => Some (Some types)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_tuple_types_round_trip :
  forall tree types,
    phase1_surface_normalize_optional_tuple_types tree = Some types ->
    phase1_surface_optional_tuple_types_tree types = tree.
Proof.
  intros tree types Hnormalize.
  unfold phase1_surface_normalize_optional_tuple_types in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_tuple_type_list_spine body)
      as [actual |] eqn:Htypes; try discriminate Hnormalize.
    inversion Hnormalize; subst types.
    unfold phase1_surface_optional_tuple_types_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_normalize_tuple_type_list_spine_round_trip
      body actual Htypes).
    reflexivity.
  - inversion Hnormalize; subst types.
    unfold phase1_surface_optional_tuple_types_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Inductive Phase1SurfaceVariantPayloadSpine : Type :=
| Phase1VariantRecordPayloadSpine
    (fields : option Phase1SurfaceFieldListSpine)
| Phase1VariantTuplePayloadSpine
    (types : option Phase1SurfaceTupleTypeListSpine).

Definition phase1_surface_variant_payload_spine_index
  (payload : Phase1SurfaceVariantPayloadSpine) : nat :=
  match payload with
  | Phase1VariantRecordPayloadSpine _ => 0
  | Phase1VariantTuplePayloadSpine _ => 1
  end.

Definition phase1_surface_variant_payload_selected_tree
  (payload : Phase1SurfaceVariantPayloadSpine) : ParseTree :=
  match payload with
  | Phase1VariantRecordPayloadSpine fields =>
      PTSequence
        [ PTLiteral "{";
          phase1_surface_optional_fields_tree fields;
          PTLiteral "}"
        ]
  | Phase1VariantTuplePayloadSpine types =>
      PTSequence
        [ PTLiteral "(";
          phase1_surface_optional_tuple_types_tree types;
          PTLiteral ")"
        ]
  end.

Definition phase1_surface_variant_payload_spine_tree
  (payload : Phase1SurfaceVariantPayloadSpine) : ParseTree :=
  PTNonterminal "variant_payload"
    (PTAlternative
      (phase1_surface_variant_payload_spine_index payload)
      (phase1_surface_variant_payload_selected_tree payload)).

Definition phase1_surface_normalize_record_variant_payload_selected
  (tree : ParseTree) : option Phase1SurfaceVariantPayloadSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (open_tree, fields_tree, close_tree) =>
          match phase1_surface_expect_literal "{" open_tree,
                phase1_surface_normalize_optional_fields fields_tree,
                phase1_surface_expect_literal "}" close_tree with
          | Some tt, Some fields, Some tt =>
              Some (Phase1VariantRecordPayloadSpine fields)
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_record_variant_payload_selected_round_trip :
  forall tree payload,
    phase1_surface_normalize_record_variant_payload_selected tree = Some payload ->
    phase1_surface_variant_payload_spine_index payload = 0 /\
    phase1_surface_variant_payload_selected_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_record_variant_payload_selected in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree fields_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "{" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_optional_fields fields_tree)
    as [fields |] eqn:Hfields; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "}" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst payload.
  split; first reflexivity.
  cbn.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items open_tree fields_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "{" open_tree Hopen).
  rewrite (phase1_surface_normalize_optional_fields_round_trip
    fields_tree fields Hfields).
  rewrite (phase1_surface_expect_literal_round_trip "}" close_tree Hclose).
  reflexivity.
Qed.

Definition phase1_surface_normalize_tuple_variant_payload_selected
  (tree : ParseTree) : option Phase1SurfaceVariantPayloadSpine :=
  match phase1_surface_expect_sequence tree with
  | Some items =>
      match phase1_surface_exact3 items with
      | Some (open_tree, types_tree, close_tree) =>
          match phase1_surface_expect_literal "(" open_tree,
                phase1_surface_normalize_optional_tuple_types types_tree,
                phase1_surface_expect_literal ")" close_tree with
          | Some tt, Some types, Some tt =>
              Some (Phase1VariantTuplePayloadSpine types)
          | _, _, _ => None
          end
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_tuple_variant_payload_selected_round_trip :
  forall tree payload,
    phase1_surface_normalize_tuple_variant_payload_selected tree = Some payload ->
    phase1_surface_variant_payload_spine_index payload = 1 /\
    phase1_surface_variant_payload_selected_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_tuple_variant_payload_selected in Hnormalize.
  destruct (phase1_surface_expect_sequence tree)
    as [items |] eqn:Hsequence; try discriminate Hnormalize.
  destruct (phase1_surface_exact3 items)
    as [[[open_tree types_tree] close_tree] |] eqn:Hitems;
    try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal "(" open_tree)
    as [[] |] eqn:Hopen; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_optional_tuple_types types_tree)
    as [types |] eqn:Htypes; try discriminate Hnormalize.
  destruct (phase1_surface_expect_literal ")" close_tree)
    as [[] |] eqn:Hclose; try discriminate Hnormalize.
  inversion Hnormalize; subst payload.
  split; first reflexivity.
  cbn.
  rewrite (phase1_surface_expect_sequence_round_trip tree items Hsequence).
  rewrite (phase1_surface_exact3_round_trip
    items open_tree types_tree close_tree Hitems).
  rewrite (phase1_surface_expect_literal_round_trip "(" open_tree Hopen).
  rewrite (phase1_surface_normalize_optional_tuple_types_round_trip
    types_tree types Htypes).
  rewrite (phase1_surface_expect_literal_round_trip ")" close_tree Hclose).
  reflexivity.
Qed.

Definition phase1_surface_normalize_variant_payload_spine
  (tree : ParseTree) : option Phase1SurfaceVariantPayloadSpine :=
  match phase1_surface_expect_nonterminal "variant_payload" tree with
  | Some body =>
      match phase1_surface_expect_alternative body with
      | Some (0, selected) =>
          phase1_surface_normalize_record_variant_payload_selected selected
      | Some (1, selected) =>
          phase1_surface_normalize_tuple_variant_payload_selected selected
      | _ => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_variant_payload_spine_round_trip :
  forall tree payload,
    phase1_surface_normalize_variant_payload_spine tree = Some payload ->
    phase1_surface_variant_payload_spine_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_variant_payload_spine in Hnormalize.
  destruct (phase1_surface_expect_nonterminal "variant_payload" tree)
    as [body |] eqn:Hnode; try discriminate Hnormalize.
  destruct (phase1_surface_expect_alternative body)
    as [[index selected] |] eqn:Halternative; try discriminate Hnormalize.
  destruct index as [|index].
  - destruct (phase1_surface_normalize_record_variant_payload_selected selected)
      as [actual |] eqn:Hselected; try discriminate Hnormalize.
    inversion Hnormalize; subst payload.
    destruct
      (phase1_surface_normalize_record_variant_payload_selected_round_trip
        selected actual Hselected)
      as [Hindex Htree].
    unfold phase1_surface_variant_payload_spine_tree.
    rewrite (phase1_surface_expect_nonterminal_round_trip
      "variant_payload" tree body Hnode).
    rewrite (phase1_surface_expect_alternative_round_trip
      body 0 selected Halternative).
    rewrite Hindex.
    rewrite Htree.
    reflexivity.
  - destruct index as [|index].
    + destruct (phase1_surface_normalize_tuple_variant_payload_selected selected)
        as [actual |] eqn:Hselected; try discriminate Hnormalize.
      inversion Hnormalize; subst payload.
      destruct
        (phase1_surface_normalize_tuple_variant_payload_selected_round_trip
          selected actual Hselected)
        as [Hindex Htree].
      unfold phase1_surface_variant_payload_spine_tree.
      rewrite (phase1_surface_expect_nonterminal_round_trip
        "variant_payload" tree body Hnode).
      rewrite (phase1_surface_expect_alternative_round_trip
        body 1 selected Halternative).
      rewrite Hindex.
      rewrite Htree.
      reflexivity.
    + discriminate Hnormalize.
Qed.

Definition phase1_surface_optional_variant_payload_spine_tree
  (payload : option Phase1SurfaceVariantPayloadSpine) : ParseTree :=
  match payload with
  | None => PTOptionalNone
  | Some value => PTOptionalSome (phase1_surface_variant_payload_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_variant_payload_spine
  (tree : ParseTree) : option (option Phase1SurfaceVariantPayloadSpine) :=
  match phase1_surface_expect_optional tree with
  | Some None => Some None
  | Some (Some body) =>
      match phase1_surface_normalize_variant_payload_spine body with
      | Some payload => Some (Some payload)
      | None => None
      end
  | None => None
  end.

Theorem phase1_surface_normalize_optional_variant_payload_spine_round_trip :
  forall tree payload,
    phase1_surface_normalize_optional_variant_payload_spine tree = Some payload ->
    phase1_surface_optional_variant_payload_spine_tree payload = tree.
Proof.
  intros tree payload Hnormalize.
  unfold phase1_surface_normalize_optional_variant_payload_spine in Hnormalize.
  destruct (phase1_surface_expect_optional tree)
    as [[body |] |] eqn:Hoptional; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_variant_payload_spine body)
      as [actual |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst payload.
    unfold phase1_surface_optional_variant_payload_spine_tree.
    rewrite (phase1_surface_expect_optional_round_trip
      tree (Some body) Hoptional).
    rewrite (phase1_surface_normalize_variant_payload_spine_round_trip
      body actual Hpayload).
    reflexivity.
  - inversion Hnormalize; subst payload.
    unfold phase1_surface_optional_variant_payload_spine_tree.
    rewrite (phase1_surface_expect_optional_round_trip tree None Hoptional).
    reflexivity.
Qed.

Record Phase1SurfaceVariantPayloadVariantSpine : Type := {
  phase1_variant_payload_variant_spine_name : string;
  phase1_variant_payload_variant_spine_payload :
    option Phase1SurfaceVariantPayloadSpine
}.

Definition phase1_surface_variant_payload_variant_spine_tree
  (variant : Phase1SurfaceVariantPayloadVariantSpine) : ParseTree :=
  PTNonterminal "variant_decl"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_variant_payload_variant_spine_name variant);
        phase1_surface_optional_variant_payload_spine_tree
          (phase1_variant_payload_variant_spine_payload variant)
      ]).

Definition phase1_surface_normalize_variant_payload_variant_spine
  (variant : Phase1SurfaceVariantSpine)
  : option Phase1SurfaceVariantPayloadVariantSpine :=
  match phase1_variant_spine_payload variant with
  | None =>
      Some
        {| phase1_variant_payload_variant_spine_name :=
             phase1_variant_spine_name variant;
           phase1_variant_payload_variant_spine_payload := None |}
  | Some payload_tree =>
      match phase1_surface_normalize_variant_payload_spine payload_tree with
      | Some payload =>
          Some
            {| phase1_variant_payload_variant_spine_name :=
                 phase1_variant_spine_name variant;
               phase1_variant_payload_variant_spine_payload := Some payload |}
      | None => None
      end
  end.

Theorem phase1_surface_normalize_variant_payload_variant_spine_round_trip :
  forall variant refined,
    phase1_surface_normalize_variant_payload_variant_spine variant = Some refined ->
    phase1_surface_variant_payload_variant_spine_tree refined =
      phase1_surface_variant_spine_tree variant.
Proof.
  intros [name [payload_tree |]] refined Hnormalize; cbn in Hnormalize.
  - destruct (phase1_surface_normalize_variant_payload_spine payload_tree)
      as [payload |] eqn:Hpayload; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    unfold phase1_surface_variant_payload_variant_spine_tree,
      phase1_surface_variant_spine_tree,
      phase1_surface_optional_variant_payload_spine_tree,
      phase1_surface_optional_variant_payload_tree.
    cbn.
    rewrite (phase1_surface_normalize_variant_payload_spine_round_trip
      payload_tree payload Hpayload).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Fixpoint phase1_surface_normalize_variant_payload_variant_spines
  (variants : list Phase1SurfaceVariantSpine)
  : option (list Phase1SurfaceVariantPayloadVariantSpine) :=
  match variants with
  | [] => Some []
  | variant :: rest =>
      match phase1_surface_normalize_variant_payload_variant_spine variant,
            phase1_surface_normalize_variant_payload_variant_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_variant_payload_variant_spines_round_trip :
  forall variants refined,
    phase1_surface_normalize_variant_payload_variant_spines variants = Some refined ->
    map phase1_surface_variant_payload_variant_spine_tree refined =
      map phase1_surface_variant_spine_tree variants.
Proof.
  intros variants.
  induction variants as [|variant rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_variant_payload_variant_spine variant)
      as [actual |] eqn:Hvariant; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_variant_payload_variant_spines rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_variant_payload_variant_spine_round_trip.
      exact Hvariant.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_variant_payload_data_suffix_tree
  (variant : Phase1SurfaceVariantPayloadVariantSpine) : ParseTree :=
  phase1_surface_data_variant_suffix_tree
    (phase1_surface_variant_payload_variant_spine_tree variant).

Lemma phase1_surface_normalize_variant_payload_variant_spines_suffix_round_trip :
  forall variants refined,
    phase1_surface_normalize_variant_payload_variant_spines variants = Some refined ->
    map phase1_surface_variant_payload_data_suffix_tree refined =
      map phase1_surface_refined_data_variant_suffix_tree variants.
Proof.
  intros variants.
  induction variants as [|variant rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_variant_payload_variant_spine variant)
      as [actual |] eqn:Hvariant; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_variant_payload_variant_spines rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    - unfold phase1_surface_variant_payload_data_suffix_tree,
        phase1_surface_refined_data_variant_suffix_tree.
      rewrite (phase1_surface_normalize_variant_payload_variant_spine_round_trip
        variant actual Hvariant).
      reflexivity.
    - eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceDataVariantPayloadSpine : Type := {
  phase1_data_variant_payload_spine_name : string;
  phase1_data_variant_payload_spine_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_data_variant_payload_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_data_variant_payload_spine_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_data_variant_payload_spine_first_variant :
    Phase1SurfaceVariantPayloadVariantSpine;
  phase1_data_variant_payload_spine_rest_variants :
    list Phase1SurfaceVariantPayloadVariantSpine
}.

Definition phase1_surface_data_variant_payload_spine_tree
  (data_value : Phase1SurfaceDataVariantPayloadSpine) : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree
          (phase1_data_variant_payload_spine_name data_value);
        phase1_surface_optional_generic_params_tree
          (phase1_data_variant_payload_spine_generic_params data_value);
        phase1_surface_optional_mode_tree
          (phase1_data_variant_payload_spine_mode data_value);
        phase1_surface_optional_generic_requirements_tree
          (phase1_data_variant_payload_spine_requirements data_value);
        PTLiteral "=";
        phase1_surface_variant_payload_variant_spine_tree
          (phase1_data_variant_payload_spine_first_variant data_value);
        PTRepetition
          (map phase1_surface_variant_payload_data_suffix_tree
            (phase1_data_variant_payload_spine_rest_variants data_value));
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_data_variant_payload_spine
  (data_value : Phase1SurfaceDataVariantSpine)
  : option Phase1SurfaceDataVariantPayloadSpine :=
  match phase1_surface_normalize_variant_payload_variant_spine
          (phase1_data_variant_spine_first_variant data_value),
        phase1_surface_normalize_variant_payload_variant_spines
          (phase1_data_variant_spine_rest_variants data_value) with
  | Some first_variant, Some rest_variants =>
      Some
        {| phase1_data_variant_payload_spine_name :=
             phase1_data_variant_spine_name data_value;
           phase1_data_variant_payload_spine_generic_params :=
             phase1_data_variant_spine_generic_params data_value;
           phase1_data_variant_payload_spine_mode :=
             phase1_data_variant_spine_mode data_value;
           phase1_data_variant_payload_spine_requirements :=
             phase1_data_variant_spine_requirements data_value;
           phase1_data_variant_payload_spine_first_variant := first_variant;
           phase1_data_variant_payload_spine_rest_variants := rest_variants |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_data_variant_payload_spine_round_trip :
  forall data_value refined,
    phase1_surface_normalize_data_variant_payload_spine data_value = Some refined ->
    phase1_surface_data_variant_payload_spine_tree refined =
      phase1_surface_data_variant_spine_tree data_value.
Proof.
  intros
    [name generic_params mode requirements first_variant rest_variants]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_variant_payload_variant_spine first_variant)
    as [first_refined |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_variant_payload_variant_spines rest_variants)
    as [rest_refined |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_data_variant_payload_spine_tree,
    phase1_surface_data_variant_spine_tree.
  cbn.
  rewrite (phase1_surface_normalize_variant_payload_variant_spine_round_trip
    first_variant first_refined Hfirst).
  rewrite
    (phase1_surface_normalize_variant_payload_variant_spines_suffix_round_trip
      rest_variants rest_refined Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_data_variant_payload_tree
  (tree : ParseTree) : option Phase1SurfaceDataVariantPayloadSpine :=
  match phase1_surface_normalize_data_variant_tree tree with
  | Some data_value => phase1_surface_normalize_data_variant_payload_spine data_value
  | None => None
  end.

Theorem phase1_surface_normalize_data_variant_payload_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_data_variant_payload_tree tree = Some refined ->
    phase1_surface_data_variant_payload_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_data_variant_payload_tree in Hnormalize.
  destruct (phase1_surface_normalize_data_variant_tree tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  transitivity (phase1_surface_data_variant_spine_tree data_value).
  - eapply phase1_surface_normalize_data_variant_payload_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_data_variant_tree_round_trip.
    exact Hdata.
Qed.
