From Stdlib Require Import Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordFieldsSpine
  GrammarAstStaticTypeArgumentCarrierSpine.

Open Scope string_scope.

(*
  Open the reusable field_decl type-expression payload left opaque by the
  record/data representation staging.

  This is intentionally one child boundary only.  Field lists, record_decl,
  and record-shaped variant payloads remain on the predecessor carrier until
  successor lift slices consume this refined field value.
*)

Record Phase1SurfaceFieldTypeSpine : Type := {
  phase1_field_type_spine_name : string;
  phase1_field_type_spine_type : Phase1SurfaceStaticTypeArgumentsTypeSpine
}.

Definition phase1_surface_field_type_spine_tree
  (field : Phase1SurfaceFieldTypeSpine) : ParseTree :=
  PTNonterminal "field_decl"
    (PTSequence
      [ phase1_surface_identifier_tree (phase1_field_type_spine_name field);
        PTLiteral ":";
        phase1_surface_static_type_arguments_type_spine_tree
          (phase1_field_type_spine_type field)
      ]).

Definition phase1_surface_normalize_field_type_spine
  (field : Phase1SurfaceFieldSpine)
  : option Phase1SurfaceFieldTypeSpine :=
  match
    phase1_surface_normalize_static_type_arguments_type_tree
      (phase1_field_spine_type_tree field)
  with
  | Some type_value =>
      Some
        {| phase1_field_type_spine_name := phase1_field_spine_name field;
           phase1_field_type_spine_type := type_value |}
  | None => None
  end.

Theorem phase1_surface_normalize_field_type_spine_round_trip :
  forall field refined,
    phase1_surface_normalize_field_type_spine field = Some refined ->
    phase1_surface_field_type_spine_tree refined =
      phase1_surface_field_spine_tree field.
Proof.
  intros [name type_tree] refined Hnormalize.
  unfold phase1_surface_normalize_field_type_spine in Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_static_type_arguments_type_tree type_tree)
    as [type_value |] eqn:Htype; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  unfold phase1_surface_field_type_spine_tree,
    phase1_surface_field_spine_tree.
  cbn.
  rewrite
    (phase1_surface_normalize_static_type_arguments_type_tree_round_trip
      type_tree type_value Htype).
  reflexivity.
Qed.

Definition phase1_surface_normalize_field_type_tree
  (tree : ParseTree) : option Phase1SurfaceFieldTypeSpine :=
  match phase1_surface_normalize_field_spine tree with
  | Some field => phase1_surface_normalize_field_type_spine field
  | None => None
  end.

Theorem phase1_surface_normalize_field_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_field_type_tree tree = Some refined ->
    phase1_surface_field_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_field_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_field_spine tree)
    as [field |] eqn:Hfield; try discriminate Hnormalize.
  transitivity (phase1_surface_field_spine_tree field).
  - eapply phase1_surface_normalize_field_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_field_spine_round_trip.
    exact Hfield.
Qed.
