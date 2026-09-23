From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceSpine
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Successor implementation-facing representation for record/data declarations
  after lifting the fallback/base-choice-refined ordinary-expression carrier
  through generic requirements.

  The earlier expression-outer implementation view remains stable for existing
  consumers. This layer advances only the generic-requirements carrier to
  Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine.
*)

Record Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration : Type := {
  phase1_expression_fallback_base_choice_impl_record_name : string;
  phase1_expression_fallback_base_choice_impl_record_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_expression_fallback_base_choice_impl_record_mode :
    option Phase1SurfaceStructuralMode;
  phase1_expression_fallback_base_choice_impl_record_requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine;
  phase1_expression_fallback_base_choice_impl_record_fields :
    option Phase1SurfaceFieldTypeListSpine
}.

Record Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration : Type := {
  phase1_expression_fallback_base_choice_impl_data_name : string;
  phase1_expression_fallback_base_choice_impl_data_generic_params :
    option Phase1SurfaceGenericParamsKindTypeSpine;
  phase1_expression_fallback_base_choice_impl_data_mode :
    option Phase1SurfaceStructuralMode;
  phase1_expression_fallback_base_choice_impl_data_requirements :
    option Phase1SurfaceGenericRequirementsExpressionFallbackBaseChoiceSpine;
  phase1_expression_fallback_base_choice_impl_data_first_variant :
    Phase1SurfaceRecordFieldTypeVariantSpine;
  phase1_expression_fallback_base_choice_impl_data_rest_variants :
    list Phase1SurfaceRecordFieldTypeVariantSpine
}.

Inductive Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDataDeclaration : Type :=
| Phase1ExpressionFallbackBaseChoiceImplementationRecordDeclaration
    (record :
      Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration)
| Phase1ExpressionFallbackBaseChoiceImplementationDataDeclaration
    (data_value :
      Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration).

Definition phase1_surface_expression_fallback_base_choice_record_to_implementation
  (record : Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceSpine)
  : Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration :=
  {| phase1_expression_fallback_base_choice_impl_record_name :=
       phase1_record_generic_requirement_expression_fallback_base_choice_spine_name
         record;
     phase1_expression_fallback_base_choice_impl_record_generic_params :=
       phase1_record_generic_requirement_expression_fallback_base_choice_spine_generic_params
         record;
     phase1_expression_fallback_base_choice_impl_record_mode :=
       phase1_record_generic_requirement_expression_fallback_base_choice_spine_mode
         record;
     phase1_expression_fallback_base_choice_impl_record_requirements :=
       phase1_record_generic_requirement_expression_fallback_base_choice_spine_requirements
         record;
     phase1_expression_fallback_base_choice_impl_record_fields :=
       phase1_record_generic_requirement_expression_fallback_base_choice_spine_fields
         record |}.

Definition phase1_surface_expression_fallback_base_choice_record_from_implementation
  (record :
    Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration)
  : Phase1SurfaceRecordGenericRequirementExpressionFallbackBaseChoiceSpine :=
  {| phase1_record_generic_requirement_expression_fallback_base_choice_spine_name :=
       phase1_expression_fallback_base_choice_impl_record_name record;
     phase1_record_generic_requirement_expression_fallback_base_choice_spine_generic_params :=
       phase1_expression_fallback_base_choice_impl_record_generic_params record;
     phase1_record_generic_requirement_expression_fallback_base_choice_spine_mode :=
       phase1_expression_fallback_base_choice_impl_record_mode record;
     phase1_record_generic_requirement_expression_fallback_base_choice_spine_requirements :=
       phase1_expression_fallback_base_choice_impl_record_requirements record;
     phase1_record_generic_requirement_expression_fallback_base_choice_spine_fields :=
       phase1_expression_fallback_base_choice_impl_record_fields record |}.

Theorem
  phase1_surface_expression_fallback_base_choice_record_implementation_round_trip :
  forall record,
    phase1_surface_expression_fallback_base_choice_record_from_implementation
      (phase1_surface_expression_fallback_base_choice_record_to_implementation
        record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Theorem
  phase1_surface_expression_fallback_base_choice_record_implementation_inverse :
  forall record,
    phase1_surface_expression_fallback_base_choice_record_to_implementation
      (phase1_surface_expression_fallback_base_choice_record_from_implementation
        record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Definition phase1_surface_expression_fallback_base_choice_data_to_implementation
  (data_value :
    Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceSpine)
  : Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration :=
  {| phase1_expression_fallback_base_choice_impl_data_name :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_name
         data_value;
     phase1_expression_fallback_base_choice_impl_data_generic_params :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_generic_params
         data_value;
     phase1_expression_fallback_base_choice_impl_data_mode :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_mode
         data_value;
     phase1_expression_fallback_base_choice_impl_data_requirements :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_requirements
         data_value;
     phase1_expression_fallback_base_choice_impl_data_first_variant :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_first_variant
         data_value;
     phase1_expression_fallback_base_choice_impl_data_rest_variants :=
       phase1_data_generic_requirement_expression_fallback_base_choice_spine_rest_variants
         data_value |}.

Definition phase1_surface_expression_fallback_base_choice_data_from_implementation
  (data_value :
    Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration)
  : Phase1SurfaceDataGenericRequirementExpressionFallbackBaseChoiceSpine :=
  {| phase1_data_generic_requirement_expression_fallback_base_choice_spine_name :=
       phase1_expression_fallback_base_choice_impl_data_name data_value;
     phase1_data_generic_requirement_expression_fallback_base_choice_spine_generic_params :=
       phase1_expression_fallback_base_choice_impl_data_generic_params data_value;
     phase1_data_generic_requirement_expression_fallback_base_choice_spine_mode :=
       phase1_expression_fallback_base_choice_impl_data_mode data_value;
     phase1_data_generic_requirement_expression_fallback_base_choice_spine_requirements :=
       phase1_expression_fallback_base_choice_impl_data_requirements data_value;
     phase1_data_generic_requirement_expression_fallback_base_choice_spine_first_variant :=
       phase1_expression_fallback_base_choice_impl_data_first_variant data_value;
     phase1_data_generic_requirement_expression_fallback_base_choice_spine_rest_variants :=
       phase1_expression_fallback_base_choice_impl_data_rest_variants data_value |}.

Theorem
  phase1_surface_expression_fallback_base_choice_data_implementation_round_trip :
  forall data_value,
    phase1_surface_expression_fallback_base_choice_data_from_implementation
      (phase1_surface_expression_fallback_base_choice_data_to_implementation
        data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Theorem
  phase1_surface_expression_fallback_base_choice_data_implementation_inverse :
  forall data_value,
    phase1_surface_expression_fallback_base_choice_data_to_implementation
      (phase1_surface_expression_fallback_base_choice_data_from_implementation
        data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Definition phase1_surface_expression_fallback_base_choice_implementation_record_tree
  (record :
    Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration)
  : ParseTree :=
  phase1_surface_record_generic_requirement_expression_fallback_base_choice_spine_tree
    (phase1_surface_expression_fallback_base_choice_record_from_implementation
      record).

Definition phase1_surface_expression_fallback_base_choice_implementation_data_tree
  (data_value :
    Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration)
  : ParseTree :=
  phase1_surface_data_generic_requirement_expression_fallback_base_choice_spine_tree
    (phase1_surface_expression_fallback_base_choice_data_from_implementation
      data_value).

Definition
  phase1_surface_expression_fallback_base_choice_implementation_record_data_tree
  (declaration :
    Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDataDeclaration)
  : ParseTree :=
  match declaration with
  | Phase1ExpressionFallbackBaseChoiceImplementationRecordDeclaration record =>
      phase1_surface_expression_fallback_base_choice_implementation_record_tree
        record
  | Phase1ExpressionFallbackBaseChoiceImplementationDataDeclaration data_value =>
      phase1_surface_expression_fallback_base_choice_implementation_data_tree
        data_value
  end.

Definition
  phase1_surface_normalize_expression_fallback_base_choice_record_implementation
  (tree : ParseTree)
  : option
      Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDeclaration :=
  match
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
      tree
  with
  | Some record =>
      Some
        (phase1_surface_expression_fallback_base_choice_record_to_implementation
          record)
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_record_implementation_round_trip :
  forall tree record,
    phase1_surface_normalize_expression_fallback_base_choice_record_implementation
      tree = Some record ->
    phase1_surface_expression_fallback_base_choice_implementation_record_tree
      record = tree.
Proof.
  intros tree record Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_record_implementation
    in Hnormalize.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst record.
  unfold
    phase1_surface_expression_fallback_base_choice_implementation_record_tree.
  rewrite
    phase1_surface_expression_fallback_base_choice_record_implementation_round_trip.
  eapply
    phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree_round_trip.
  exact Hrefined.
Qed.

Definition
  phase1_surface_normalize_expression_fallback_base_choice_data_implementation
  (tree : ParseTree)
  : option
      Phase1SurfaceExpressionFallbackBaseChoiceImplementationDataDeclaration :=
  match
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
      tree
  with
  | Some data_value =>
      Some
        (phase1_surface_expression_fallback_base_choice_data_to_implementation
          data_value)
  | None => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_data_implementation_round_trip :
  forall tree data_value,
    phase1_surface_normalize_expression_fallback_base_choice_data_implementation
      tree = Some data_value ->
    phase1_surface_expression_fallback_base_choice_implementation_data_tree
      data_value = tree.
Proof.
  intros tree data_value Hnormalize.
  unfold
    phase1_surface_normalize_expression_fallback_base_choice_data_implementation
    in Hnormalize.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree
      tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst data_value.
  unfold
    phase1_surface_expression_fallback_base_choice_implementation_data_tree.
  rewrite
    phase1_surface_expression_fallback_base_choice_data_implementation_round_trip.
  eapply
    phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_round_trip.
  exact Hrefined.
Qed.

Definition
  phase1_surface_normalize_expression_fallback_base_choice_record_data_declaration_spine
  (declaration : Phase1SurfaceDeclarationSpine)
  : option
      Phase1SurfaceExpressionFallbackBaseChoiceImplementationRecordDataDeclaration :=
  match phase1_declaration_spine_tag declaration with
  | Phase1RecordDeclaration =>
      match
        phase1_surface_normalize_expression_fallback_base_choice_record_implementation
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some record =>
          Some
            (Phase1ExpressionFallbackBaseChoiceImplementationRecordDeclaration
              record)
      | None => None
      end
  | Phase1DataDeclaration =>
      match
        phase1_surface_normalize_expression_fallback_base_choice_data_implementation
          (phase1_declaration_spine_selected_tree declaration)
      with
      | Some data_value =>
          Some
            (Phase1ExpressionFallbackBaseChoiceImplementationDataDeclaration
              data_value)
      | None => None
      end
  | _ => None
  end.

Theorem
  phase1_surface_normalize_expression_fallback_base_choice_record_data_declaration_spine_round_trip :
  forall declaration refined,
    phase1_surface_normalize_expression_fallback_base_choice_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_expression_fallback_base_choice_implementation_record_data_tree
      refined = phase1_declaration_spine_selected_tree declaration.
Proof.
  intros [tag selected_tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct
      (phase1_surface_normalize_expression_fallback_base_choice_record_implementation
        selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply
      phase1_surface_normalize_expression_fallback_base_choice_record_implementation_round_trip.
    exact Hrecord.
  - destruct
      (phase1_surface_normalize_expression_fallback_base_choice_data_implementation
        selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply
      phase1_surface_normalize_expression_fallback_base_choice_data_implementation_round_trip.
    exact Hdata.
Qed.

Theorem
  phase1_surface_certified_record_has_expression_fallback_base_choice_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists record,
      phase1_surface_normalize_expression_fallback_base_choice_record_implementation
        tree = Some record /\
      phase1_surface_expression_fallback_base_choice_implementation_record_tree
        record = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists
    (phase1_surface_expression_fallback_base_choice_record_to_implementation
      refined).
  split.
  - unfold
      phase1_surface_normalize_expression_fallback_base_choice_record_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold
      phase1_surface_expression_fallback_base_choice_implementation_record_tree.
    rewrite
      phase1_surface_expression_fallback_base_choice_record_implementation_round_trip.
    exact Htree.
Qed.

Theorem
  phase1_surface_certified_data_has_expression_fallback_base_choice_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists data_value,
      phase1_surface_normalize_expression_fallback_base_choice_data_implementation
        tree = Some data_value /\
      phase1_surface_expression_fallback_base_choice_implementation_data_tree
        data_value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_generic_requirement_expression_fallback_base_choice_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists
    (phase1_surface_expression_fallback_base_choice_data_to_implementation
      refined).
  split.
  - unfold
      phase1_surface_normalize_expression_fallback_base_choice_data_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold
      phase1_surface_expression_fallback_base_choice_implementation_data_tree.
    rewrite
      phase1_surface_expression_fallback_base_choice_data_implementation_round_trip.
    exact Htree.
Qed.
