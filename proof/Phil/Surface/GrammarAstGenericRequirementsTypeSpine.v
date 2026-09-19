From Stdlib Require Import Lists.List.

From Phil.Surface Require Import
  GrammarAstGenericRequirementsSpine
  GrammarAstGenericRequirementTypeSpine.

Import ListNotations.

(*
  Lift the generic-requirement type refinement through generic_requirements and
  its optional wrapper.

  Proposition and effect-set payloads remain exact certified ParseTree values
  inside Phase1SurfaceGenericRequirementTypeSpine.
*)

Fixpoint phase1_surface_normalize_generic_requirement_type_values
  (requirements : list Phase1SurfaceGenericRequirementSpine)
  : option (list Phase1SurfaceGenericRequirementTypeSpine) :=
  match requirements with
  | [] => Some []
  | requirement :: rest =>
      match phase1_surface_normalize_generic_requirement_type_spine requirement,
            phase1_surface_normalize_generic_requirement_type_values rest with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem phase1_surface_normalize_generic_requirement_type_values_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirement_type_values requirements =
      Some refined ->
    map phase1_surface_generic_requirement_type_spine_tree refined =
      map phase1_surface_generic_requirement_spine_tree requirements.
Proof.
  intros requirements.
  induction requirements as [|requirement rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_type_spine requirement)
      as [actual |] eqn:Hrequirement; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_type_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply phase1_surface_normalize_generic_requirement_type_spine_round_trip.
      exact Hrequirement.
    + eapply IH.
      exact Hrest.
Qed.

Record Phase1SurfaceGenericRequirementsTypeSpine : Type := {
  phase1_generic_requirements_type_spine_entries :
    list Phase1SurfaceGenericRequirementTypeSpine
}.

Definition phase1_surface_generic_requirements_type_spine_tree
  (requirements : Phase1SurfaceGenericRequirementsTypeSpine) : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [ PTLiteral "requires";
        PTLiteral "{";
        PTRepetition
          (map phase1_surface_generic_requirement_type_spine_tree
            (phase1_generic_requirements_type_spine_entries requirements));
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_generic_requirements_type_spine
  (requirements : Phase1SurfaceGenericRequirementsSpine)
  : option Phase1SurfaceGenericRequirementsTypeSpine :=
  match
    phase1_surface_normalize_generic_requirement_type_values
      (phase1_generic_requirements_spine_entries requirements)
  with
  | Some entries =>
      Some
        {| phase1_generic_requirements_type_spine_entries := entries |}
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirements_type_spine_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirements_type_spine requirements =
      Some refined ->
    phase1_surface_generic_requirements_type_spine_tree refined =
      phase1_surface_generic_requirements_spine_tree requirements.
Proof.
  intros [entries] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_type_values entries)
    as [actual |] eqn:Hentries; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_requirement_type_values_round_trip
      entries actual Hentries).
  reflexivity.
Qed.

Definition phase1_surface_optional_generic_requirements_type_tree
  (requirements : option Phase1SurfaceGenericRequirementsTypeSpine)
  : ParseTree :=
  match requirements with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (phase1_surface_generic_requirements_type_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_generic_requirements_type
  (requirements : option Phase1SurfaceGenericRequirementsSpine)
  : option (option Phase1SurfaceGenericRequirementsTypeSpine) :=
  match requirements with
  | None => Some None
  | Some value =>
      match phase1_surface_normalize_generic_requirements_type_spine value with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_type_round_trip :
  forall requirements refined,
    phase1_surface_normalize_optional_generic_requirements_type requirements =
      Some refined ->
    phase1_surface_optional_generic_requirements_type_tree refined =
      phase1_surface_optional_generic_requirements_tree requirements.
Proof.
  intros [requirements |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirements_type_spine requirements)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirements_type_spine_round_trip
        requirements actual Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirements_type_tree
  (tree : ParseTree) : option Phase1SurfaceGenericRequirementsTypeSpine :=
  match phase1_surface_normalize_generic_requirements_spine tree with
  | Some requirements =>
      phase1_surface_normalize_generic_requirements_type_spine requirements
  | None => None
  end.

Theorem phase1_surface_normalize_generic_requirements_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirements_type_tree tree =
      Some refined ->
    phase1_surface_generic_requirements_type_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirements_type_tree in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirements_spine tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity (phase1_surface_generic_requirements_spine_tree requirements).
  - eapply phase1_surface_normalize_generic_requirements_type_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirements_spine_round_trip.
    exact Hrequirements.
Qed.

Definition phase1_surface_normalize_optional_generic_requirements_type_tree
  (tree : ParseTree)
  : option (option Phase1SurfaceGenericRequirementsTypeSpine) :=
  match phase1_surface_normalize_optional_generic_requirements tree with
  | Some requirements =>
      phase1_surface_normalize_optional_generic_requirements_type requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_type_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_optional_generic_requirements_type_tree tree =
      Some refined ->
    phase1_surface_optional_generic_requirements_type_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_optional_generic_requirements_type_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_optional_generic_requirements tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity (phase1_surface_optional_generic_requirements_tree requirements).
  - eapply
      phase1_surface_normalize_optional_generic_requirements_type_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_optional_generic_requirements_round_trip.
    exact Hrequirements.
Qed.
