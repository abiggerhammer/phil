From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstFieldTypeSpine.

Import ListNotations.

(*
  Lift the refined field_decl type-expression payload from #1161/#1162
  through the existing comma-separated field-list carrier.

  The optional-fields wrapper and enclosing record/data declarations remain
  on their predecessor carriers for successor slices.
*)

Definition phase1_surface_field_type_suffix_tree
  (field : Phase1SurfaceFieldTypeSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_field_type_spine_tree field
    ].

Fixpoint phase1_surface_normalize_field_type_values
  (fields : list Phase1SurfaceFieldSpine)
  : option (list Phase1SurfaceFieldTypeSpine) :=
  match fields with
  | [] => Some []
  | field :: rest =>
      match phase1_surface_normalize_field_type_spine field,
            phase1_surface_normalize_field_type_values rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_field_type_values_round_trip :
  forall fields refined,
    phase1_surface_normalize_field_type_values fields = Some refined ->
    map phase1_surface_field_type_spine_tree refined =
      map phase1_surface_field_spine_tree fields.
Proof.
  intros fields.
  induction fields as [|field rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_field_type_spine field)
      as [actual |] eqn:Hfield; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_field_type_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_field_type_spine_round_trip.
      exact Hfield.
    + eapply IH.
      exact Hrest.
Qed.

Theorem phase1_surface_normalize_field_type_suffix_values_round_trip :
  forall fields refined,
    phase1_surface_normalize_field_type_values fields = Some refined ->
    map phase1_surface_field_type_suffix_tree refined =
      map phase1_surface_field_suffix_tree fields.
Proof.
  intros fields.
  induction fields as [|field rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct (phase1_surface_normalize_field_type_spine field)
      as [actual |] eqn:Hfield; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_field_type_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + unfold phase1_surface_field_type_suffix_tree,
        phase1_surface_field_suffix_tree.
      rewrite
        (phase1_surface_normalize_field_type_spine_round_trip
          field actual Hfield).
      reflexivity.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceFieldTypeListSpine : Type := {
  phase1_field_type_list_spine_first : Phase1SurfaceFieldTypeSpine;
  phase1_field_type_list_spine_rest : list Phase1SurfaceFieldTypeSpine;
  phase1_field_type_list_spine_trailing_comma : bool
}.

Definition phase1_surface_field_type_list_spine_tree
  (fields : Phase1SurfaceFieldTypeListSpine) : ParseTree :=
  PTSequence
    [ phase1_surface_field_type_spine_tree
        (phase1_field_type_list_spine_first fields);
      PTRepetition
        (map phase1_surface_field_type_suffix_tree
          (phase1_field_type_list_spine_rest fields));
      phase1_surface_trailing_comma_tree
        (phase1_field_type_list_spine_trailing_comma fields)
    ].

Definition phase1_surface_normalize_field_type_list_spine
  (fields : Phase1SurfaceFieldListSpine)
  : option Phase1SurfaceFieldTypeListSpine :=
  match
    phase1_surface_normalize_field_type_spine
      (phase1_field_list_spine_first fields),
    phase1_surface_normalize_field_type_values
      (phase1_field_list_spine_rest fields)
  with
  | Some first, Some rest =>
      Some
        {| phase1_field_type_list_spine_first := first;
           phase1_field_type_list_spine_rest := rest;
           phase1_field_type_list_spine_trailing_comma :=
             phase1_field_list_spine_trailing_comma fields |}
  | _, _ => None
  end.

Theorem phase1_surface_normalize_field_type_list_spine_round_trip :
  forall fields refined,
    phase1_surface_normalize_field_type_list_spine fields = Some refined ->
    phase1_surface_field_type_list_spine_tree refined =
      phase1_surface_field_list_spine_tree fields.
Proof.
  intros [first rest trailing] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_field_type_spine first)
    as [actual_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_field_type_values rest)
    as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_field_type_spine_round_trip
      first actual_first Hfirst).
  rewrite
    (phase1_surface_normalize_field_type_suffix_values_round_trip
      rest actual_rest Hrest).
  reflexivity.
Qed.
