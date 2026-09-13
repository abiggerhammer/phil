From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstStaticArgumentsSpine
  GrammarAstRefinementTupleTypePayloadSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Refine the type-valued static_argument branch using the already-complete
  nonreference type carrier.  The session, static-value, and effect-set
  argument branches remain exact selected ParseTree values for successors.
*)

Definition phase1_surface_normalize_complete_nonreference_type_spine
  (tree : ParseTree)
  : option Phase1SurfaceRefinementTupleNonreferenceTypeSpine :=
  match phase1_surface_normalize_nonreference_type_spine tree with
  | Some outer =>
      match phase1_surface_normalize_primitive_nonreference_type_spine outer with
      | Some primitive =>
          match
            phase1_surface_normalize_shallow_compound_nonreference_type_spine
              primitive
          with
          | Some shallow =>
              phase1_surface_normalize_refinement_tuple_nonreference_type_spine
                shallow
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem
  phase1_surface_normalize_complete_nonreference_type_spine_round_trip :
  forall tree refined,
    phase1_surface_normalize_complete_nonreference_type_spine tree =
      Some refined ->
    phase1_surface_refinement_tuple_nonreference_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_complete_nonreference_type_spine in Hnormalize.
  destruct (phase1_surface_normalize_nonreference_type_spine tree)
    as [outer |] eqn:Houter; try discriminate Hnormalize.
  destruct (phase1_surface_normalize_primitive_nonreference_type_spine outer)
    as [primitive |] eqn:Hprimitive; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_shallow_compound_nonreference_type_spine primitive)
    as [shallow |] eqn:Hshallow; try discriminate Hnormalize.
  transitivity
    (phase1_surface_shallow_compound_nonreference_type_spine_tree shallow).
  - eapply
      phase1_surface_normalize_refinement_tuple_nonreference_type_spine_round_trip.
    exact Hnormalize.
  - transitivity
      (phase1_surface_primitive_nonreference_type_spine_tree primitive).
    + eapply
        phase1_surface_normalize_shallow_compound_nonreference_type_spine_round_trip.
      exact Hshallow.
    + transitivity (phase1_surface_nonreference_type_spine_tree outer).
      * eapply
          phase1_surface_normalize_primitive_nonreference_type_spine_round_trip.
        exact Hprimitive.
      * eapply phase1_surface_normalize_nonreference_type_spine_round_trip.
        exact Houter.
Qed.

Inductive Phase1SurfaceStaticTypeArgumentSpine : Type :=
| Phase1StaticRefinedTypeArgument
    (type_value : Phase1SurfaceRefinementTupleNonreferenceTypeSpine)
| Phase1StaticOpaqueSessionArgument
    (selected_tree : ParseTree)
| Phase1StaticOpaqueValueArgument
    (selected_tree : ParseTree)
| Phase1StaticOpaqueEffectSetArgument
    (selected_tree : ParseTree).

Definition phase1_surface_static_type_argument_spine_tree
  (argument : Phase1SurfaceStaticTypeArgumentSpine) : ParseTree :=
  match argument with
  | Phase1StaticRefinedTypeArgument type_value =>
      PTNonterminal "static_argument"
        (PTAlternative 0
          (phase1_surface_refinement_tuple_nonreference_type_spine_tree
            type_value))
  | Phase1StaticOpaqueSessionArgument selected_tree =>
      PTNonterminal "static_argument" (PTAlternative 1 selected_tree)
  | Phase1StaticOpaqueValueArgument selected_tree =>
      PTNonterminal "static_argument" (PTAlternative 2 selected_tree)
  | Phase1StaticOpaqueEffectSetArgument selected_tree =>
      PTNonterminal "static_argument" (PTAlternative 3 selected_tree)
  end.

Definition phase1_surface_normalize_static_type_argument_spine
  (argument : Phase1SurfaceStaticArgumentSpine)
  : option Phase1SurfaceStaticTypeArgumentSpine :=
  match phase1_static_argument_spine_tag argument with
  | Phase1StaticTypeArgument =>
      match
        phase1_surface_normalize_complete_nonreference_type_spine
          (phase1_static_argument_spine_selected_tree argument)
      with
      | Some type_value => Some (Phase1StaticRefinedTypeArgument type_value)
      | None => None
      end
  | Phase1StaticSessionArgument =>
      Some
        (Phase1StaticOpaqueSessionArgument
          (phase1_static_argument_spine_selected_tree argument))
  | Phase1StaticValueArgument =>
      Some
        (Phase1StaticOpaqueValueArgument
          (phase1_static_argument_spine_selected_tree argument))
  | Phase1StaticEffectSetArgument =>
      Some
        (Phase1StaticOpaqueEffectSetArgument
          (phase1_static_argument_spine_selected_tree argument))
  end.

Theorem phase1_surface_normalize_static_type_argument_spine_round_trip :
  forall argument refined,
    phase1_surface_normalize_static_type_argument_spine argument = Some refined ->
    phase1_surface_static_type_argument_spine_tree refined =
      phase1_surface_static_argument_spine_tree argument.
Proof.
  intros [tag selected] refined Hnormalize.
  destruct tag; cbn in Hnormalize.
  - destruct (phase1_surface_normalize_complete_nonreference_type_spine selected)
      as [type_value |] eqn:Htype; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_complete_nonreference_type_spine_round_trip
        selected type_value Htype).
    reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
  - inversion Hnormalize; subst refined. reflexivity.
Qed.

Definition phase1_surface_normalize_static_type_argument_tree
  (tree : ParseTree) : option Phase1SurfaceStaticTypeArgumentSpine :=
  match phase1_surface_normalize_static_argument_spine tree with
  | Some argument => phase1_surface_normalize_static_type_argument_spine argument
  | None => None
  end.

Theorem phase1_surface_normalize_static_type_argument_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_static_type_argument_tree tree = Some refined ->
    phase1_surface_static_type_argument_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_static_type_argument_tree in Hnormalize.
  destruct (phase1_surface_normalize_static_argument_spine tree)
    as [argument |] eqn:Hargument; try discriminate Hnormalize.
  transitivity (phase1_surface_static_argument_spine_tree argument).
  - eapply phase1_surface_normalize_static_type_argument_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_static_argument_spine_round_trip.
    exact Hargument.
Qed.
