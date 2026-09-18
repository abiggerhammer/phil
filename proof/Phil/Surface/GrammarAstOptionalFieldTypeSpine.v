From Phil.Surface Require Import
  GrammarAstFieldTypeListSpine.

(*
  Lift the refined field-list type payload through the optional-fields wrapper.

  The enclosing record/data declarations remain on their predecessor carriers
  for successor slices.
*)

Definition phase1_surface_optional_field_type_list_tree
  (fields : option Phase1SurfaceFieldTypeListSpine) : ParseTree :=
  match fields with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome (phase1_surface_field_type_list_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_field_type_list
  (fields : option Phase1SurfaceFieldListSpine)
  : option (option Phase1SurfaceFieldTypeListSpine) :=
  match fields with
  | None => Some None
  | Some value =>
      match phase1_surface_normalize_field_type_list_spine value with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem phase1_surface_normalize_optional_field_type_list_round_trip :
  forall fields refined,
    phase1_surface_normalize_optional_field_type_list fields = Some refined ->
    phase1_surface_optional_field_type_list_tree refined =
      phase1_surface_optional_fields_tree fields.
Proof.
  intros [fields |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_field_type_list_spine fields)
      as [actual |] eqn:Hfields; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_field_type_list_spine_round_trip
        fields actual Hfields).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_optional_field_type_tree
  (tree : ParseTree) : option (option Phase1SurfaceFieldTypeListSpine) :=
  match phase1_surface_normalize_optional_fields tree with
  | Some fields => phase1_surface_normalize_optional_field_type_list fields
  | None => None
  end.

Theorem phase1_surface_normalize_optional_field_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_optional_field_type_tree tree = Some refined ->
    phase1_surface_optional_field_type_list_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_optional_field_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_optional_fields tree)
    as [fields |] eqn:Hfields; try discriminate Hnormalize.
  transitivity (phase1_surface_optional_fields_tree fields).
  - eapply phase1_surface_normalize_optional_field_type_list_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_optional_fields_round_trip.
    exact Hfields.
Qed.
