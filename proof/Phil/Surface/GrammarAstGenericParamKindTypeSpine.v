From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamsSpine
  GrammarAstGenericKindTypeSpine.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the typed generic-kind payload refinement through generic_param,
  generic_params, and the optional generic-parameter wrapper.

  Declaration carriers remain on the predecessor optional generic-parameter
  representation for successor slices.
*)

Record Phase1SurfaceGenericParamKindTypeSpine : Type := {
  phase1_generic_param_kind_type_spine_name : string;
  phase1_generic_param_kind_type_spine_kind : Phase1SurfaceGenericKindTypeSpine
}.

Definition phase1_surface_generic_param_kind_type_spine_tree
  (parameter : Phase1SurfaceGenericParamKindTypeSpine) : ParseTree :=
  PTNonterminal "generic_param"
    (PTSequence
      [ phase1_surface_identifier_tree
          (phase1_generic_param_kind_type_spine_name parameter);
        PTLiteral ":";
        phase1_surface_generic_kind_type_spine_tree
          (phase1_generic_param_kind_type_spine_kind parameter)
      ]).

Definition phase1_surface_normalize_generic_param_kind_type_spine
  (parameter : Phase1SurfaceGenericParamSpine)
  : option Phase1SurfaceGenericParamKindTypeSpine :=
  match
    phase1_surface_normalize_generic_kind_type_spine
      (phase1_generic_param_spine_kind parameter)
  with
  | Some kind =>
      Some
        {| phase1_generic_param_kind_type_spine_name :=
             phase1_generic_param_spine_name parameter;
           phase1_generic_param_kind_type_spine_kind := kind |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_param_kind_type_spine_round_trip :
  forall parameter refined,
    phase1_surface_normalize_generic_param_kind_type_spine parameter =
      Some refined ->
    phase1_surface_generic_param_kind_type_spine_tree refined =
      phase1_surface_generic_param_spine_tree parameter.
Proof.
  intros [name kind] refined Hnormalize.
  cbn in Hnormalize.
  destruct (phase1_surface_normalize_generic_kind_type_spine kind)
    as [actual |] eqn:Hkind; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_kind_type_spine_round_trip
      kind actual Hkind).
  reflexivity.
Qed.

Definition phase1_surface_generic_param_kind_type_suffix_tree
  (parameter : Phase1SurfaceGenericParamKindTypeSpine) : ParseTree :=
  PTSequence
    [ PTLiteral ",";
      phase1_surface_generic_param_kind_type_spine_tree parameter
    ].

Fixpoint phase1_surface_normalize_generic_param_kind_type_values
  (parameters : list Phase1SurfaceGenericParamSpine)
  : option (list Phase1SurfaceGenericParamKindTypeSpine) :=
  match parameters with
  | [] => Some []
  | parameter :: rest =>
      match
        phase1_surface_normalize_generic_param_kind_type_spine parameter,
        phase1_surface_normalize_generic_param_kind_type_values rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_generic_param_kind_type_values_round_trip :
  forall parameters refined,
    phase1_surface_normalize_generic_param_kind_type_values parameters =
      Some refined ->
    map phase1_surface_generic_param_kind_type_spine_tree refined =
      map phase1_surface_generic_param_spine_tree parameters.
Proof.
  intros parameters.
  induction parameters as [|parameter rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_param_kind_type_spine parameter)
      as [actual |] eqn:Hparameter; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_generic_param_kind_type_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_generic_param_kind_type_spine_round_trip.
      exact Hparameter.
    + eapply IH.
      exact Hrest.
Qed.

Theorem
  phase1_surface_normalize_generic_param_kind_type_suffix_values_round_trip :
  forall parameters refined,
    phase1_surface_normalize_generic_param_kind_type_values parameters =
      Some refined ->
    map phase1_surface_generic_param_kind_type_suffix_tree refined =
      map phase1_surface_generic_param_suffix_tree parameters.
Proof.
  intros parameters.
  induction parameters as [|parameter rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_param_kind_type_spine parameter)
      as [actual |] eqn:Hparameter; try discriminate Hnormalize.
    destruct (phase1_surface_normalize_generic_param_kind_type_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + unfold phase1_surface_generic_param_kind_type_suffix_tree,
        phase1_surface_generic_param_suffix_tree.
      rewrite
        (phase1_surface_normalize_generic_param_kind_type_spine_round_trip
          parameter actual Hparameter).
      reflexivity.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGenericParamsKindTypeSpine : Type := {
  phase1_generic_params_kind_type_spine_first :
    Phase1SurfaceGenericParamKindTypeSpine;
  phase1_generic_params_kind_type_spine_rest :
    list Phase1SurfaceGenericParamKindTypeSpine
}.

Definition phase1_surface_generic_params_kind_type_spine_tree
  (parameters : Phase1SurfaceGenericParamsKindTypeSpine) : ParseTree :=
  PTNonterminal "generic_params"
    (PTSequence
      [ PTLiteral "[";
        phase1_surface_generic_param_kind_type_spine_tree
          (phase1_generic_params_kind_type_spine_first parameters);
        PTRepetition
          (map phase1_surface_generic_param_kind_type_suffix_tree
            (phase1_generic_params_kind_type_spine_rest parameters));
        PTLiteral "]"
      ]).

Definition phase1_surface_normalize_generic_params_kind_type_spine
  (parameters : Phase1SurfaceGenericParamsSpine)
  : option Phase1SurfaceGenericParamsKindTypeSpine :=
  match
    phase1_surface_normalize_generic_param_kind_type_spine
      (phase1_generic_params_spine_first parameters),
    phase1_surface_normalize_generic_param_kind_type_values
      (phase1_generic_params_spine_rest parameters)
  with
  | Some first, Some rest =>
      Some
        {| phase1_generic_params_kind_type_spine_first := first;
           phase1_generic_params_kind_type_spine_rest := rest |}
  | _, _ => None
  end.

Theorem
  phase1_surface_normalize_generic_params_kind_type_spine_round_trip :
  forall parameters refined,
    phase1_surface_normalize_generic_params_kind_type_spine parameters =
      Some refined ->
    phase1_surface_generic_params_kind_type_spine_tree refined =
      phase1_surface_generic_params_spine_tree parameters.
Proof.
  intros [first rest] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_param_kind_type_spine first)
    as [actual_first |] eqn:Hfirst; try discriminate Hnormalize.
  destruct
    (phase1_surface_normalize_generic_param_kind_type_values rest)
    as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_param_kind_type_spine_round_trip
      first actual_first Hfirst).
  rewrite
    (phase1_surface_normalize_generic_param_kind_type_suffix_values_round_trip
      rest actual_rest Hrest).
  reflexivity.
Qed.

Definition phase1_surface_optional_generic_params_kind_type_tree
  (parameters : option Phase1SurfaceGenericParamsKindTypeSpine) : ParseTree :=
  match parameters with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome (phase1_surface_generic_params_kind_type_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_generic_params_kind_type
  (parameters : option Phase1SurfaceGenericParamsSpine)
  : option (option Phase1SurfaceGenericParamsKindTypeSpine) :=
  match parameters with
  | None => Some None
  | Some value =>
      match phase1_surface_normalize_generic_params_kind_type_spine value with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_generic_params_kind_type_round_trip :
  forall parameters refined,
    phase1_surface_normalize_optional_generic_params_kind_type parameters =
      Some refined ->
    phase1_surface_optional_generic_params_kind_type_tree refined =
      phase1_surface_optional_generic_params_tree parameters.
Proof.
  intros [parameters |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_params_kind_type_spine parameters)
      as [actual |] eqn:Hparameters; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_params_kind_type_spine_round_trip
        parameters actual Hparameters).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_generic_params_kind_type_tree
  (tree : ParseTree) : option Phase1SurfaceGenericParamsKindTypeSpine :=
  match phase1_surface_normalize_generic_params_spine tree with
  | Some parameters =>
      phase1_surface_normalize_generic_params_kind_type_spine parameters
  | None => None
  end.

Theorem phase1_surface_normalize_generic_params_kind_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_params_kind_type_tree tree = Some refined ->
    phase1_surface_generic_params_kind_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_params_kind_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_params_spine tree)
    as [parameters |] eqn:Hparameters; try discriminate Hnormalize.
  transitivity (phase1_surface_generic_params_spine_tree parameters).
  - eapply phase1_surface_normalize_generic_params_kind_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_params_spine_round_trip.
    exact Hparameters.
Qed.
