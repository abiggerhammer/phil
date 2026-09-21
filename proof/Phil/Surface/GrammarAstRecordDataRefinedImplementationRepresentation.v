From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementEffectsSpine
  GrammarAstRecordDataGenericRequirementEffectsTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Successor implementation-facing representation for the fully refined
  record/data correspondence chain.

  GrammarAstRecordDataImplementationRepresentation intentionally stopped at
  earlier shallow carriers.  This layer leaves that bridge stable for its
  existing consumers and adds an isomorphic implementation view over the
  current end-of-chain record/data spines.

  The only remaining explicit syntax boundary inside these carriers is the
  ordinary expression ParseTree retained by term_arguments.
*)

Record Phase1SurfaceRefinedImplementationRecordDeclaration : Type := {
  phase1_refined_impl_record_name : string;
  phase1_refined_impl_record_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_refined_impl_record_mode : option Phase1SurfaceStructuralMode;
  phase1_refined_impl_record_requirements :
    option Phase1SurfaceGenericRequirementsEffectsSpine;
  phase1_refined_impl_record_fields : option Phase1SurfaceFieldTypeListSpine
}.

Record Phase1SurfaceRefinedImplementationDataDeclaration : Type := {
  phase1_refined_impl_data_name : string;
  phase1_refined_impl_data_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_refined_impl_data_mode : option Phase1SurfaceStructuralMode;
  phase1_refined_impl_data_requirements :
    option Phase1SurfaceGenericRequirementsEffectsSpine;
  phase1_refined_impl_data_first_variant :
    Phase1SurfaceRecordFieldTypeVariantSpine;
  phase1_refined_impl_data_rest_variants :
    list Phase1SurfaceRecordFieldTypeVariantSpine
}.

Inductive Phase1SurfaceRefinedImplementationRecordDataDeclaration : Type :=
| Phase1RefinedImplementationRecordDeclaration
    (record : Phase1SurfaceRefinedImplementationRecordDeclaration)
| Phase1RefinedImplementationDataDeclaration
    (data_value : Phase1SurfaceRefinedImplementationDataDeclaration).

Definition phase1_surface_refined_record_to_implementation
  (record : Phase1SurfaceRecordGenericRequirementEffectsSpine)
  : Phase1SurfaceRefinedImplementationRecordDeclaration :=
  {| phase1_refined_impl_record_name :=
       phase1_record_generic_requirement_effects_spine_name record;
     phase1_refined_impl_record_generic_params :=
       phase1_record_generic_requirement_effects_spine_generic_params record;
     phase1_refined_impl_record_mode :=
       phase1_record_generic_requirement_effects_spine_mode record;
     phase1_refined_impl_record_requirements :=
       phase1_record_generic_requirement_effects_spine_requirements record;
     phase1_refined_impl_record_fields :=
       phase1_record_generic_requirement_effects_spine_fields record |}.

Definition phase1_surface_refined_record_from_implementation
  (record : Phase1SurfaceRefinedImplementationRecordDeclaration)
  : Phase1SurfaceRecordGenericRequirementEffectsSpine :=
  {| phase1_record_generic_requirement_effects_spine_name :=
       phase1_refined_impl_record_name record;
     phase1_record_generic_requirement_effects_spine_generic_params :=
       phase1_refined_impl_record_generic_params record;
     phase1_record_generic_requirement_effects_spine_mode :=
       phase1_refined_impl_record_mode record;
     phase1_record_generic_requirement_effects_spine_requirements :=
       phase1_refined_impl_record_requirements record;
     phase1_record_generic_requirement_effects_spine_fields :=
       phase1_refined_impl_record_fields record |}.

Theorem phase1_surface_refined_record_implementation_round_trip :
  forall record,
    phase1_surface_refined_record_from_implementation
      (phase1_surface_refined_record_to_implementation record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Theorem phase1_surface_refined_record_implementation_inverse :
  forall record,
    phase1_surface_refined_record_to_implementation
      (phase1_surface_refined_record_from_implementation record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Definition phase1_surface_refined_data_to_implementation
  (data_value : Phase1SurfaceDataGenericRequirementEffectsSpine)
  : Phase1SurfaceRefinedImplementationDataDeclaration :=
  {| phase1_refined_impl_data_name :=
       phase1_data_generic_requirement_effects_spine_name data_value;
     phase1_refined_impl_data_generic_params :=
       phase1_data_generic_requirement_effects_spine_generic_params data_value;
     phase1_refined_impl_data_mode :=
       phase1_data_generic_requirement_effects_spine_mode data_value;
     phase1_refined_impl_data_requirements :=
       phase1_data_generic_requirement_effects_spine_requirements data_value;
     phase1_refined_impl_data_first_variant :=
       phase1_data_generic_requirement_effects_spine_first_variant data_value;
     phase1_refined_impl_data_rest_variants :=
       phase1_data_generic_requirement_effects_spine_rest_variants data_value |}.

Definition phase1_surface_refined_data_from_implementation
  (data_value : Phase1SurfaceRefinedImplementationDataDeclaration)
  : Phase1SurfaceDataGenericRequirementEffectsSpine :=
  {| phase1_data_generic_requirement_effects_spine_name :=
       phase1_refined_impl_data_name data_value;
     phase1_data_generic_requirement_effects_spine_generic_params :=
       phase1_refined_impl_data_generic_params data_value;
     phase1_data_generic_requirement_effects_spine_mode :=
       phase1_refined_impl_data_mode data_value;
     phase1_data_generic_requirement_effects_spine_requirements :=
       phase1_refined_impl_data_requirements data_value;
     phase1_data_generic_requirement_effects_spine_first_variant :=
       phase1_refined_impl_data_first_variant data_value;
     phase1_data_generic_requirement_effects_spine_rest_variants :=
       phase1_refined_impl_data_rest_variants data_value |}.

Theorem phase1_surface_refined_data_implementation_round_trip :
  forall data_value,
    phase1_surface_refined_data_from_implementation
      (phase1_surface_refined_data_to_implementation data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Theorem phase1_surface_refined_data_implementation_inverse :
  forall data_value,
    phase1_surface_refined_data_to_implementation
      (phase1_surface_refined_data_from_implementation data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Definition phase1_surface_refined_implementation_record_tree
  (record : Phase1SurfaceRefinedImplementationRecordDeclaration) : ParseTree :=
  phase1_surface_record_generic_requirement_effects_spine_tree
    (phase1_surface_refined_record_from_implementation record).

Definition phase1_surface_refined_implementation_data_tree
  (data_value : Phase1SurfaceRefinedImplementationDataDeclaration) : ParseTree :=
  phase1_surface_data_generic_requirement_effects_spine_tree
    (phase1_surface_refined_data_from_implementation data_value).

Definition phase1_surface_refined_implementation_record_data_tree
  (declaration : Phase1SurfaceRefinedImplementationRecordDataDeclaration)
  : ParseTree :=
  match declaration with
  | Phase1RefinedImplementationRecordDeclaration record =>
      phase1_surface_refined_implementation_record_tree record
  | Phase1RefinedImplementationDataDeclaration data_value =>
      phase1_surface_refined_implementation_data_tree data_value
  end.

Definition phase1_surface_normalize_refined_record_implementation
  (tree : ParseTree)
  : option Phase1SurfaceRefinedImplementationRecordDeclaration :=
  match
    phase1_surface_normalize_record_generic_requirement_effects_tree tree
  with
  | Some record =>
      Some (phase1_surface_refined_record_to_implementation record)
  | None => None
  end.

Theorem
  phase1_surface_normalize_refined_record_implementation_round_trip :
  forall tree record,
    phase1_surface_normalize_refined_record_implementation tree =
      Some record ->
    phase1_surface_refined_implementation_record_tree record = tree.
Proof.
  intros tree record Hnormalize.
  unfold phase1_surface_normalize_refined_record_implementation in Hnormalize.
  destruct
    (phase1_surface_normalize_record_generic_requirement_effects_tree tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst record.
  unfold phase1_surface_refined_implementation_record_tree.
  rewrite phase1_surface_refined_record_implementation_round_trip.
  eapply
    phase1_surface_normalize_record_generic_requirement_effects_tree_round_trip.
  exact Hrefined.
Qed.

Definition phase1_surface_normalize_refined_data_implementation
  (tree : ParseTree)
  : option Phase1SurfaceRefinedImplementationDataDeclaration :=
  match
    phase1_surface_normalize_data_generic_requirement_effects_tree tree
  with
  | Some data_value =>
      Some (phase1_surface_refined_data_to_implementation data_value)
  | None => None
  end.

Theorem
  phase1_surface_normalize_refined_data_implementation_round_trip :
  forall tree data_value,
    phase1_surface_normalize_refined_data_implementation tree =
      Some data_value ->
    phase1_surface_refined_implementation_data_tree data_value = tree.
Proof.
  intros tree data_value Hnormalize.
  unfold phase1_surface_normalize_refined_data_implementation in Hnormalize.
  destruct
    (phase1_surface_normalize_data_generic_requirement_effects_tree tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst data_value.
  unfold phase1_surface_refined_implementation_data_tree.
  rewrite phase1_surface_refined_data_implementation_round_trip.
  eapply
    phase1_surface_normalize_data_generic_requirement_effects_tree_round_trip.
  exact Hrefined.
Qed.

Definition phase1_surface_normalize_refined_record_data_declaration_spine
  (declaration : Phase1SurfaceDeclarationSpine)
  : option Phase1SurfaceRefinedImplementationRecordDataDeclaration :=
  match phase1_declaration_spine_tag declaration with
  | Phase1RecordDeclaration =>
      match
        phase1_surface_normalize_refined_record_implementation
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some record =>
          Some (Phase1RefinedImplementationRecordDeclaration record)
      | None => None
      end
  | Phase1DataDeclaration =>
      match
        phase1_surface_normalize_refined_data_implementation
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some data_value =>
          Some (Phase1RefinedImplementationDataDeclaration data_value)
      | None => None
      end
  | _ => None
  end.

Theorem
  phase1_surface_normalize_refined_record_data_declaration_spine_round_trip :
  forall declaration refined,
    phase1_surface_normalize_refined_record_data_declaration_spine declaration =
      Some refined ->
    phase1_surface_refined_implementation_record_data_tree refined =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros [tag selected_tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_refined_record_implementation selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply
      phase1_surface_normalize_refined_record_implementation_round_trip.
    exact Hrecord.
  - destruct
      (phase1_surface_normalize_refined_data_implementation selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply phase1_surface_normalize_refined_data_implementation_round_trip.
    exact Hdata.
Qed.

Theorem phase1_surface_certified_record_has_refined_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists record,
      phase1_surface_normalize_refined_record_implementation tree = Some record /\
      phase1_surface_refined_implementation_record_tree record = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_generic_requirement_effects_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists (phase1_surface_refined_record_to_implementation refined).
  split.
  - unfold phase1_surface_normalize_refined_record_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_refined_implementation_record_tree.
    rewrite phase1_surface_refined_record_implementation_round_trip.
    exact Htree.
Qed.

Theorem phase1_surface_certified_data_has_refined_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists data_value,
      phase1_surface_normalize_refined_data_implementation tree =
        Some data_value /\
      phase1_surface_refined_implementation_data_tree data_value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_generic_requirement_effects_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists (phase1_surface_refined_data_to_implementation refined).
  split.
  - unfold phase1_surface_normalize_refined_data_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_refined_implementation_data_tree.
    rewrite phase1_surface_refined_data_implementation_round_trip.
    exact Htree.
Qed.
