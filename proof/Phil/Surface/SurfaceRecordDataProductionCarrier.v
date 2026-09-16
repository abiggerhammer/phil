From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstGenericParamsSpine
  GrammarAstStructuralModeSpine
  GrammarAstGenericRequirementsSpine
  GrammarAstRecordFieldsSpine
  GrammarAstVariantPayloadSpine
  GrammarAstRecordDataImplementationRepresentation.

Import ListNotations.

(*
  Compact production carrier for the record/data representation staged by
  GrammarAstRecordDataImplementationRepresentation.

  The staged representation is exact but intentionally still contains nested
  ParseTree payloads whose recursive type/proposition/effect correspondence is
  outside this tranche.  Production ASTs already erase some purely syntactic
  distinctions as well (for example an empty `requires {}` versus no requires
  clause, and a record-field trailing comma).

  This carrier therefore exposes exactly the common certified semantic surface:

  - declaration names;
  - generic parameter names and the closed generic-kind tag;
  - structural mode;
  - ordered generic-requirement tags;
  - ordered record-field names;
  - ordered data-variant names;
  - variant payload kind, record-payload field names, and tuple arity.

  Recursive payload contents are deliberately erased here.  The projection
  functions below are defined from the #986 implementation representation, so
  this is a projection of that certified carrier rather than a second parser or
  an independent semantic representation.
*)

Inductive Phase1SurfaceProductionGenericKind : Type :=
| Phase1ProductionTypeGenericKind
| Phase1ProductionNatGenericKind
| Phase1ProductionSessionGenericKind
| Phase1ProductionMessageGenericKind
| Phase1ProductionEffectsGenericKind
| Phase1ProductionProviderGenericKind
| Phase1ProductionCallableGenericKind
| Phase1ProductionBoundaryGenericKind
| Phase1ProductionArchitectureGenericKind.

Inductive Phase1SurfaceProductionStructuralMode : Type :=
| Phase1ProductionUnrestrictedMode
| Phase1ProductionAffineMode
| Phase1ProductionLinearMode.

Inductive Phase1SurfaceProductionRequirement : Type :=
| Phase1ProductionStructuralRequirement
| Phase1ProductionPropositionRequirement
| Phase1ProductionProviderRequirement
| Phase1ProductionCallableRequirement
| Phase1ProductionBoundaryRequirement
| Phase1ProductionArchitectureRequirement
| Phase1ProductionEffectsRequirement
| Phase1ProductionAuthorityRequirement
| Phase1ProductionBoundaryRepresentationRequirement
| Phase1ProductionRepresentationRequirement
| Phase1ProductionPlacementRequirement
| Phase1ProductionCostRequirement
| Phase1ProductionEnvironmentRequirement.

Record Phase1SurfaceProductionGenericParam : Type := {
  phase1_production_generic_param_name : string;
  phase1_production_generic_param_kind : Phase1SurfaceProductionGenericKind
}.

Inductive Phase1SurfaceProductionVariantPayload : Type :=
| Phase1ProductionRecordPayload (fields : list string)
| Phase1ProductionTuplePayload (types : list unit).

Record Phase1SurfaceProductionVariant : Type := {
  phase1_production_variant_name : string;
  phase1_production_variant_payload : option Phase1SurfaceProductionVariantPayload
}.

Inductive Phase1SurfaceProductionRecordDataDeclaration : Type :=
| Phase1ProductionRecordDeclaration
    (name : string)
    (generic_params : list Phase1SurfaceProductionGenericParam)
    (mode : option Phase1SurfaceProductionStructuralMode)
    (requirements : list Phase1SurfaceProductionRequirement)
    (fields : list string)
| Phase1ProductionDataDeclaration
    (name : string)
    (generic_params : list Phase1SurfaceProductionGenericParam)
    (mode : option Phase1SurfaceProductionStructuralMode)
    (requirements : list Phase1SurfaceProductionRequirement)
    (variants : list Phase1SurfaceProductionVariant).

Definition phase1_surface_make_production_generic_param
  (name : string)
  (kind : Phase1SurfaceProductionGenericKind)
  : Phase1SurfaceProductionGenericParam :=
  {| phase1_production_generic_param_name := name;
     phase1_production_generic_param_kind := kind |}.

Definition phase1_surface_make_production_record_payload
  (fields : list string)
  : Phase1SurfaceProductionVariantPayload :=
  Phase1ProductionRecordPayload fields.

Definition phase1_surface_make_production_tuple_payload
  (types : list unit)
  : Phase1SurfaceProductionVariantPayload :=
  Phase1ProductionTuplePayload types.

Definition phase1_surface_make_production_variant
  (name : string)
  (payload : option Phase1SurfaceProductionVariantPayload)
  : Phase1SurfaceProductionVariant :=
  {| phase1_production_variant_name := name;
     phase1_production_variant_payload := payload |}.

Definition phase1_surface_make_production_record
  (name : string)
  (generic_params : list Phase1SurfaceProductionGenericParam)
  (mode : option Phase1SurfaceProductionStructuralMode)
  (requirements : list Phase1SurfaceProductionRequirement)
  (fields : list string)
  : Phase1SurfaceProductionRecordDataDeclaration :=
  Phase1ProductionRecordDeclaration name generic_params mode requirements fields.

Definition phase1_surface_make_production_data
  (name : string)
  (generic_params : list Phase1SurfaceProductionGenericParam)
  (mode : option Phase1SurfaceProductionStructuralMode)
  (requirements : list Phase1SurfaceProductionRequirement)
  (variants : list Phase1SurfaceProductionVariant)
  : Phase1SurfaceProductionRecordDataDeclaration :=
  Phase1ProductionDataDeclaration name generic_params mode requirements variants.

Definition phase1_surface_generic_kind_tag_to_production
  (tag : Phase1SurfaceGenericKindTag)
  : Phase1SurfaceProductionGenericKind :=
  match tag with
  | Phase1TypeGenericKind => Phase1ProductionTypeGenericKind
  | Phase1NatGenericKind => Phase1ProductionNatGenericKind
  | Phase1SessionGenericKind => Phase1ProductionSessionGenericKind
  | Phase1MessageGenericKind => Phase1ProductionMessageGenericKind
  | Phase1EffectsGenericKind => Phase1ProductionEffectsGenericKind
  | Phase1ProviderGenericKind => Phase1ProductionProviderGenericKind
  | Phase1CallableGenericKind => Phase1ProductionCallableGenericKind
  | Phase1BoundaryGenericKind => Phase1ProductionBoundaryGenericKind
  | Phase1ArchitectureGenericKind => Phase1ProductionArchitectureGenericKind
  end.

Definition phase1_surface_structural_mode_to_production
  (mode : Phase1SurfaceStructuralMode)
  : Phase1SurfaceProductionStructuralMode :=
  match mode with
  | Phase1UnrestrictedMode => Phase1ProductionUnrestrictedMode
  | Phase1AffineMode => Phase1ProductionAffineMode
  | Phase1LinearMode => Phase1ProductionLinearMode
  end.

Definition phase1_surface_requirement_tag_to_production
  (tag : Phase1SurfaceGenericRequirementTag)
  : Phase1SurfaceProductionRequirement :=
  match tag with
  | Phase1StructuralRequirement => Phase1ProductionStructuralRequirement
  | Phase1PropositionRequirement => Phase1ProductionPropositionRequirement
  | Phase1ProviderRequirement => Phase1ProductionProviderRequirement
  | Phase1CallableRequirement => Phase1ProductionCallableRequirement
  | Phase1BoundaryRequirement => Phase1ProductionBoundaryRequirement
  | Phase1ArchitectureRequirement => Phase1ProductionArchitectureRequirement
  | Phase1EffectsRequirement => Phase1ProductionEffectsRequirement
  | Phase1AuthorityRequirement => Phase1ProductionAuthorityRequirement
  | Phase1BoundaryRepresentationRequirement =>
      Phase1ProductionBoundaryRepresentationRequirement
  | Phase1RepresentationRequirement => Phase1ProductionRepresentationRequirement
  | Phase1PlacementRequirement => Phase1ProductionPlacementRequirement
  | Phase1CostRequirement => Phase1ProductionCostRequirement
  | Phase1EnvironmentRequirement => Phase1ProductionEnvironmentRequirement
  end.

Definition phase1_surface_generic_param_to_production
  (parameter : Phase1SurfaceGenericParamSpine)
  : Phase1SurfaceProductionGenericParam :=
  phase1_surface_make_production_generic_param
    (phase1_generic_param_spine_name parameter)
    (phase1_surface_generic_kind_tag_to_production
      (phase1_generic_kind_spine_tag
        (phase1_generic_param_spine_kind parameter))).

Definition phase1_surface_generic_params_to_production
  (parameters : option Phase1SurfaceGenericParamsSpine)
  : list Phase1SurfaceProductionGenericParam :=
  match parameters with
  | None => []
  | Some values =>
      phase1_surface_generic_param_to_production
        (phase1_generic_params_spine_first values) ::
      map phase1_surface_generic_param_to_production
        (phase1_generic_params_spine_rest values)
  end.

Definition phase1_surface_mode_to_production
  (mode : option Phase1SurfaceStructuralMode)
  : option Phase1SurfaceProductionStructuralMode :=
  match mode with
  | None => None
  | Some value => Some (phase1_surface_structural_mode_to_production value)
  end.

Definition phase1_surface_requirements_to_production
  (requirements : option Phase1SurfaceGenericRequirementsSpine)
  : list Phase1SurfaceProductionRequirement :=
  match requirements with
  | None => []
  | Some values =>
      map
        (fun requirement =>
          phase1_surface_requirement_tag_to_production
            (phase1_generic_requirement_spine_tag requirement))
        (phase1_generic_requirements_spine_entries values)
  end.

Definition phase1_surface_fields_to_production
  (fields : option Phase1SurfaceFieldListSpine)
  : list string :=
  match fields with
  | None => []
  | Some values =>
      phase1_field_spine_name (phase1_field_list_spine_first values) ::
      map phase1_field_spine_name (phase1_field_list_spine_rest values)
  end.

Definition phase1_surface_tuple_types_to_production
  (types : option Phase1SurfaceTupleTypeListSpine)
  : list unit :=
  match types with
  | None => []
  | Some values =>
      tt :: map (fun _ => tt) (phase1_tuple_type_list_spine_rest values)
  end.

Definition phase1_surface_variant_payload_to_production
  (payload : option Phase1SurfaceVariantPayloadSpine)
  : option Phase1SurfaceProductionVariantPayload :=
  match payload with
  | None => None
  | Some (Phase1VariantRecordPayloadSpine fields) =>
      Some
        (phase1_surface_make_production_record_payload
          (phase1_surface_fields_to_production fields))
  | Some (Phase1VariantTuplePayloadSpine types) =>
      Some
        (phase1_surface_make_production_tuple_payload
          (phase1_surface_tuple_types_to_production types))
  end.

Definition phase1_surface_variant_to_production
  (variant : Phase1SurfaceVariantPayloadVariantSpine)
  : Phase1SurfaceProductionVariant :=
  phase1_surface_make_production_variant
    (phase1_variant_payload_variant_spine_name variant)
    (phase1_surface_variant_payload_to_production
      (phase1_variant_payload_variant_spine_payload variant)).

Definition phase1_surface_record_to_production_carrier
  (record : Phase1SurfaceImplementationRecordDeclaration)
  : Phase1SurfaceProductionRecordDataDeclaration :=
  phase1_surface_make_production_record
    (phase1_impl_record_name record)
    (phase1_surface_generic_params_to_production
      (phase1_impl_record_generic_params record))
    (phase1_surface_mode_to_production (phase1_impl_record_mode record))
    (phase1_surface_requirements_to_production
      (phase1_impl_record_requirements record))
    (phase1_surface_fields_to_production (phase1_impl_record_fields record)).

Definition phase1_surface_data_to_production_carrier
  (data_value : Phase1SurfaceImplementationDataDeclaration)
  : Phase1SurfaceProductionRecordDataDeclaration :=
  phase1_surface_make_production_data
    (phase1_impl_data_name data_value)
    (phase1_surface_generic_params_to_production
      (phase1_impl_data_generic_params data_value))
    (phase1_surface_mode_to_production (phase1_impl_data_mode data_value))
    (phase1_surface_requirements_to_production
      (phase1_impl_data_requirements data_value))
    (phase1_surface_variant_to_production
      (phase1_impl_data_first_variant data_value) ::
     map phase1_surface_variant_to_production
      (phase1_impl_data_rest_variants data_value)).

Definition phase1_surface_record_data_to_production_carrier
  (declaration : Phase1SurfaceImplementationRecordDataDeclaration)
  : Phase1SurfaceProductionRecordDataDeclaration :=
  match declaration with
  | Phase1ImplementationRecordDeclaration record =>
      phase1_surface_record_to_production_carrier record
  | Phase1ImplementationDataDeclaration data_value =>
      phase1_surface_data_to_production_carrier data_value
  end.

Theorem phase1_surface_record_to_production_uses_carrier :
  forall record,
    phase1_surface_record_to_production_carrier record =
    phase1_surface_make_production_record
      (phase1_impl_record_name record)
      (phase1_surface_generic_params_to_production
        (phase1_impl_record_generic_params record))
      (phase1_surface_mode_to_production (phase1_impl_record_mode record))
      (phase1_surface_requirements_to_production
        (phase1_impl_record_requirements record))
      (phase1_surface_fields_to_production (phase1_impl_record_fields record)).
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_data_to_production_uses_carrier :
  forall data_value,
    phase1_surface_data_to_production_carrier data_value =
    phase1_surface_make_production_data
      (phase1_impl_data_name data_value)
      (phase1_surface_generic_params_to_production
        (phase1_impl_data_generic_params data_value))
      (phase1_surface_mode_to_production (phase1_impl_data_mode data_value))
      (phase1_surface_requirements_to_production
        (phase1_impl_data_requirements data_value))
      (phase1_surface_variant_to_production
        (phase1_impl_data_first_variant data_value) ::
       map phase1_surface_variant_to_production
        (phase1_impl_data_rest_variants data_value)).
Proof.
  reflexivity.
Qed.
