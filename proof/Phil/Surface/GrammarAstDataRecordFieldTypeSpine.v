From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstVariantPayloadSpine
  GrammarAstVariantDeclRecordFieldTypeSpine.

Import ListNotations.

(*
  Lift the record-field-type-refined variant_decl carrier through the ordered
  data-variant list and enclosing data_decl.

  The data name, generic parameters, structural mode, and generic
  requirements are already refined by the predecessor carrier and remain
  unchanged.
*)

Fixpoint phase1_surface_normalize_record_field_type_variant_spines
  (variants : list Phase1SurfaceVariantPayloadVariantSpine)
  : option (list Phase1SurfaceRecordFieldTypeVariantSpine) :=
  match variants with
  | [] => Some []
  | variant :: rest =>
      match phase1_surface_normalize_record_field_type_variant_spine variant,
            phase1_surface_normalize_record_field_type_variant_spines rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_record_field_type_variant_spines_round_trip :
  forall variants refined,
    phase1_surface_normalize_record_field_type_variant_spines variants =
      Some refined ->
    map phase1_surface_record_field_type_variant_spine_tree refined =
      map phase1_surface_variant_payload_variant_spine_tree variants.
Proof.
  intros variants.
  induction variants as [|variant rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_record_field_type_variant_spine variant)
      as [actual |] eqn:Hvariant; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_record_field_type_variant_spines rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_record_field_type_variant_spine_round_trip.
      exact Hvariant.
    + eapply IH.
      exact Hrest.
Qed.

Definition phase1_surface_record_field_type_data_suffix_tree
  (variant : Phase1SurfaceRecordFieldTypeVariantSpine) : ParseTree :=
  phase1_surface_data_variant_suffix_tree
    (phase1_surface_record_field_type_variant_spine_tree variant).

Lemma
  phase1_surface_normalize_record_field_type_variant_spines_suffix_round_trip :
  forall variants refined,
    phase1_surface_normalize_record_field_type_variant_spines variants =
      Some refined ->
    map phase1_surface_record_field_type_data_suffix_tree refined =
      map phase1_surface_variant_payload_data_suffix_tree variants.
Proof.
  intros variants.
  induction variants as [|variant rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_record_field_type_variant_spine variant)
      as [actual |] eqn:Hvariant; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_record_field_type_variant_spines rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + unfold phase1_surface_record_field_type_data_suffix_tree,
        phase1_surface_variant_payload_data_suffix_tree.
      rewrite
        (phase1_surface_normalize_record_field_type_variant_spine_round_trip
          variant actual Hvariant).
      reflexivity.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceDataRecordFieldTypeSpine : Type := {
  phase1_data_record_field_type_spine_name : string;
  phase1_data_record_field_type_spine_generic_params :
    option Phase1SurfaceGenericParamsSpine;
  phase1_data_record_field_type_spine_mode : option Phase1SurfaceStructuralMode;
  phase1_data_record_field_type_spine_requirements :
    option Phase1SurfaceGenericRequirementsSpine;
  phase1_data_record_field_type_spine_first_variant :
    Phase1SurfaceRecordFieldTypeVariantSpine;
  phase1_data_record_field_type_spine_rest_variants :
    list Phase1SurfaceRecordFieldTypeVariantSpine
}.

Definition phase1_surface_data_record_field_type_spine_tree
  (data_value : Phase1SurfaceDataRecordFieldTypeSpine) : ParseTree :=
  PTNonterminal "data_decl"
    (PTSequence
      [ PTLiteral "data";
        phase1_surface_identifier_tree
          (phase1_data_record_field_type_spine_name data_value);
        phase1_surface_optional_generic_params_tree
          (phase1_data_record_field_type_spine_generic_params data_value);
        phase1_surface_optional_mode_tree
          (phase1_data_record_field_type_spine_mode data_value);
        phase1_surface_optional_generic_requirements_tree
          (phase1_data_record_field_type_spine_requirements data_value);
        PTLiteral "=";
        phase1_surface_record_field_type_variant_spine_tree
          (phase1_data_record_field_type_spine_first_variant data_value);
        PTRepetition
          (map phase1_surface_record_field_type_data_suffix_tree
            (phase1_data_record_field_type_spine_rest_variants data_value));
        PTLiteral ";"
      ]).

Definition phase1_surface_normalize_data_record_field_type_spine
  (data_value : Phase1SurfaceDataVariantPayloadSpine)
  : option Phase1SurfaceDataRecordFieldTypeSpine :=
  match
    phase1_surface_normalize_record_field_type_variant_spine
      (phase1_data_variant_payload_spine_first_variant data_value),
    phase1_surface_normalize_record_field_type_variant_spines
      (phase1_data_variant_payload_spine_rest_variants data_value)
  with
  | Some first_variant, Some rest_variants =>
      Some
        {| phase1_data_record_field_type_spine_name :=
             phase1_data_variant_payload_spine_name data_value;
           phase1_data_record_field_type_spine_generic_params :=
             phase1_data_variant_payload_spine_generic_params data_value;
           phase1_data_record_field_type_spine_mode :=
             phase1_data_variant_payload_spine_mode data_value;
           phase1_data_record_field_type_spine_requirements :=
             phase1_data_variant_payload_spine_requirements data_value;
           phase1_data_record_field_type_spine_first_variant := first_variant;
           phase1_data_record_field_type_spine_rest_variants := rest_variants |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_data_record_field_type_spine_round_trip :
  forall data_value refined,
    phase1_surface_normalize_data_record_field_type_spine data_value =
      Some refined ->
    phase1_surface_data_record_field_type_spine_tree refined =
      phase1_surface_data_variant_payload_spine_tree data_value.
Proof.
  intros
    [name generic_params mode requirements first_variant rest_variants]
    refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_record_field_type_variant_spine first_variant)
    as [first_refined |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_record_field_type_variant_spines rest_variants)
    as [rest_refined |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_record_field_type_variant_spine_round_trip
      first_variant first_refined Hfirst).
  rewrite
    (phase1_surface_normalize_record_field_type_variant_spines_suffix_round_trip
      rest_variants rest_refined Hrest).
  reflexivity.
Qed.

Definition phase1_surface_normalize_data_record_field_type_tree
  (tree : ParseTree) : option Phase1SurfaceDataRecordFieldTypeSpine :=
  match phase1_surface_normalize_data_variant_payload_tree tree with
  | Some data_value =>
      phase1_surface_normalize_data_record_field_type_spine data_value
  | None => None
  end.

Theorem phase1_surface_normalize_data_record_field_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_data_record_field_type_tree tree = Some refined ->
    phase1_surface_data_record_field_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_data_record_field_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_data_variant_payload_tree tree)
    as [data_value |] eqn:Hdata; try discriminate Hnormalize.
  transitivity (phase1_surface_data_variant_payload_spine_tree data_value).
  - eapply phase1_surface_normalize_data_record_field_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_data_variant_payload_tree_round_trip.
    exact Hdata.
Qed.
