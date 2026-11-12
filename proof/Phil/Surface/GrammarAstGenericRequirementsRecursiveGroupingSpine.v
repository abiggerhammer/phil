From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstGenericRequirementsPropositionSpine
  GrammarAstGenericRequirementRecursiveGroupingSpine.

Import ListNotations.
Open Scope string_scope.

(*
  PHIL-SURFACE-GRAMMAR-CORR-001 G3: lift canonical recursive grouping
  through ordered generic_requirements and the optional wrapper.
  Every member now holds the complete thirteen-way refined carrier;
  the Effects child is no longer opaque. No declaration consumers change.
*)

Fixpoint phase1_surface_normalize_generic_requirement_recursive_grouping_values
  (requirements : list Phase1SurfaceGenericRequirementPropositionSpine)
  : option (list Phase1SurfaceGenericRequirementRecursiveGroupingSpine) :=
  match requirements with
  | [] => Some []
  | requirement :: rest =>
      match
        phase1_surface_normalize_generic_requirement_recursive_grouping_spine requirement,
        phase1_surface_normalize_generic_requirement_recursive_grouping_values rest
      with
      | Some refined, Some refined_rest => Some (refined :: refined_rest)
      | _, _ => None
      end
  end.

Theorem
  phase1_surface_normalize_generic_requirement_recursive_grouping_values_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirement_recursive_grouping_values requirements =
      Some refined ->
    map phase1_surface_generic_requirement_recursive_grouping_spine_tree refined =
      map phase1_surface_generic_requirement_proposition_spine_tree requirements.
Proof.
  intros requirements.
  induction requirements as [|requirement rest IH]; intros refined Hnormalize.
  - cbn in Hnormalize.
    inversion Hnormalize; subst refined.
    reflexivity.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_recursive_grouping_spine requirement)
      as [actual |] eqn:Hrequirement; try discriminate Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirement_recursive_grouping_values rest)
      as [actual_rest |] eqn:Hrest; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    f_equal.
    + eapply
        phase1_surface_normalize_generic_requirement_recursive_grouping_spine_round_trip.
      exact Hrequirement.
    + eapply IH.
      reflexivity.
Qed.

Record Phase1SurfaceGenericRequirementsRecursiveGroupingSpine : Type := {
  phase1_generic_requirements_recursive_grouping_spine_entries :
    list Phase1SurfaceGenericRequirementRecursiveGroupingSpine
}.

Definition phase1_surface_generic_requirements_recursive_grouping_spine_tree
  (requirements : Phase1SurfaceGenericRequirementsRecursiveGroupingSpine)
  : ParseTree :=
  PTNonterminal "generic_requirements"
    (PTSequence
      [ PTLiteral "requires";
        PTLiteral "{";
        PTRepetition
          (map phase1_surface_generic_requirement_recursive_grouping_spine_tree
            (phase1_generic_requirements_recursive_grouping_spine_entries
              requirements));
        PTLiteral "}"
      ]).

Definition phase1_surface_normalize_generic_requirements_recursive_grouping_spine
  (requirements : Phase1SurfaceGenericRequirementsPropositionSpine)
  : option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine :=
  match
    phase1_surface_normalize_generic_requirement_recursive_grouping_values
      (phase1_generic_requirements_proposition_spine_entries requirements)
  with
  | Some entries =>
      Some
        {| phase1_generic_requirements_recursive_grouping_spine_entries := entries |}
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_recursive_grouping_spine_round_trip :
  forall requirements refined,
    phase1_surface_normalize_generic_requirements_recursive_grouping_spine
      requirements = Some refined ->
    phase1_surface_generic_requirements_recursive_grouping_spine_tree refined =
      phase1_surface_generic_requirements_proposition_spine_tree requirements.
Proof.
  intros [entries] refined Hnormalize.
  cbn in Hnormalize.
  destruct
    (phase1_surface_normalize_generic_requirement_recursive_grouping_values entries)
    as [actual |] eqn:Hentries; try discriminate Hnormalize.
  inversion Hnormalize; subst refined.
  cbn.
  rewrite
    (phase1_surface_normalize_generic_requirement_recursive_grouping_values_round_trip
      entries actual Hentries).
  reflexivity.
Qed.

Definition phase1_surface_optional_generic_requirements_recursive_grouping_tree
  (requirements : option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine)
  : ParseTree :=
  match requirements with
  | None => PTOptionalNone
  | Some value =>
      PTOptionalSome
        (phase1_surface_generic_requirements_recursive_grouping_spine_tree value)
  end.

Definition phase1_surface_normalize_optional_generic_requirements_recursive_grouping
  (requirements : option Phase1SurfaceGenericRequirementsPropositionSpine)
  : option (option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine) :=
  match requirements with
  | None => Some None
  | Some value =>
      match
        phase1_surface_normalize_generic_requirements_recursive_grouping_spine value
      with
      | Some refined => Some (Some refined)
      | None => None
      end
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_round_trip :
  forall requirements refined,
    phase1_surface_normalize_optional_generic_requirements_recursive_grouping
      requirements = Some refined ->
    phase1_surface_optional_generic_requirements_recursive_grouping_tree refined =
      phase1_surface_optional_generic_requirements_proposition_tree requirements.
Proof.
  intros [requirements |] refined Hnormalize.
  - cbn in Hnormalize.
    destruct
      (phase1_surface_normalize_generic_requirements_recursive_grouping_spine
        requirements)
      as [actual |] eqn:Hrequirements; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    rewrite
      (phase1_surface_normalize_generic_requirements_recursive_grouping_spine_round_trip
        requirements actual Hrequirements).
    reflexivity.
  - inversion Hnormalize; subst refined.
    reflexivity.
Qed.

Definition phase1_surface_normalize_generic_requirements_recursive_grouping_tree
  (tree : ParseTree)
  : option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine :=
  match phase1_surface_normalize_generic_requirements_proposition_tree tree with
  | Some requirements =>
      phase1_surface_normalize_generic_requirements_recursive_grouping_spine
        requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_generic_requirements_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_generic_requirements_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_generic_requirements_recursive_grouping_spine_tree refined = tree.
Proof.
  intros tree refined Hnormalize.
  unfold phase1_surface_normalize_generic_requirements_recursive_grouping_tree
    in Hnormalize.
  destruct (phase1_surface_normalize_generic_requirements_proposition_tree tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_generic_requirements_proposition_spine_tree requirements).
  - eapply
      phase1_surface_normalize_generic_requirements_recursive_grouping_spine_round_trip.
    exact Hnormalize.
  - eapply phase1_surface_normalize_generic_requirements_proposition_tree_round_trip.
    exact Hrequirements.
Qed.

Definition
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
  (tree : ParseTree)
  : option (option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine) :=
  match phase1_surface_normalize_optional_generic_requirements_proposition_tree tree with
  | Some requirements =>
      phase1_surface_normalize_optional_generic_requirements_recursive_grouping
        requirements
  | None => None
  end.

Theorem
  phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree_round_trip :
  forall tree refined,
    phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree tree =
      Some refined ->
    phase1_surface_optional_generic_requirements_recursive_grouping_tree refined =
      tree.
Proof.
  intros tree refined Hnormalize.
  unfold
    phase1_surface_normalize_optional_generic_requirements_recursive_grouping_tree
    in Hnormalize.
  destruct
    (phase1_surface_normalize_optional_generic_requirements_proposition_tree tree)
    as [requirements |] eqn:Hrequirements; try discriminate Hnormalize.
  transitivity
    (phase1_surface_optional_generic_requirements_proposition_tree requirements).
  - eapply
      phase1_surface_normalize_optional_generic_requirements_recursive_grouping_round_trip.
    exact Hnormalize.
  - eapply
      phase1_surface_normalize_optional_generic_requirements_proposition_tree_round_trip.
    exact Hrequirements.
Qed.
