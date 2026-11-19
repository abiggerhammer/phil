From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarDerivation
  GrammarAstTopLevelSpine
  GrammarAstStructuralModeSpine
  GrammarAstFieldTypeSpine
  GrammarAstGenericKindTypeSpine
  GrammarAstGenericParamKindTypeSpine
  GrammarAstGenericRequirementRecursiveGroupingSpine
  GrammarAstGenericRequirementsRecursiveGroupingSpine
  GrammarAstFieldTypeListSpine
  GrammarAstVariantPayloadSpine
  GrammarAstVariantRecordFieldTypeSpine
  GrammarAstVariantDeclRecordFieldTypeSpine
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation
  GrammarAstRecordDataRecursiveGroupingImplementationAdmissionExamples
  GrammarAstRecordDataRecursiveGroupingTaggedAdmission
  GrammarAstRecordDataRecursiveGroupingAcceptedKeyExtensionality
  GrammarAstRecordDataRecursiveGroupingAdmissionImageFibers.

Import ListNotations.
Open Scope string_scope.

(*
  Bounded PHIL-SURFACE-GRAMMAR-CORR-001 G3 production-observable
  projection of the exact recursive-grouping Record/Data implementation
  carrier. It retains the semantic surface of the older compact
  projection: tag, declaration name, ordered generic names/kind indices,
  structural mode, ordered requirement indices, record-field names,
  and variant names/payload shape/tuple arity.

  This view intentionally erases recursive type/proposition/effect
  interiors, spelling/trailing commas, and optional requirement presence
  when there are zero members. It is not injective and is NOT a binding
  to Phil's production Haskell AST or parser. The exact source-preserving
  carrier remains the authority for G3 admission and fiber equality.
*)

Inductive Phase1SurfaceRecursiveGroupingObservedPayload : Type :=
| Phase1ObservedNoPayload
| Phase1ObservedRecordPayload (field_names : list string)
| Phase1ObservedTuplePayload (arity : nat).

Record Phase1SurfaceRecursiveGroupingObservedVariant : Type := {
  phase1_observed_variant_name : string;
  phase1_observed_variant_payload : Phase1SurfaceRecursiveGroupingObservedPayload
}.

Inductive Phase1SurfaceRecursiveGroupingObservedRecordData : Type :=
| Phase1ObservedRecord
    (name : string)
    (generic_params : list (string * nat))
    (mode : option Phase1SurfaceStructuralMode)
    (requirement_tags : list nat)
    (field_names : list string)
| Phase1ObservedData
    (name : string)
    (generic_params : list (string * nat))
    (mode : option Phase1SurfaceStructuralMode)
    (requirement_tags : list nat)
    (variants : list Phase1SurfaceRecursiveGroupingObservedVariant).

Definition phase1_surface_observe_recursive_grouping_generic_param
  (parameter : Phase1SurfaceGenericParamKindTypeSpine) : string * nat :=
  (phase1_generic_param_kind_type_spine_name parameter,
   phase1_surface_generic_kind_type_spine_index
     (phase1_generic_param_kind_type_spine_kind parameter)).

Definition phase1_surface_observe_recursive_grouping_generic_params
  (parameters : option Phase1SurfaceGenericParamsKindTypeSpine)
  : list (string * nat) :=
  match parameters with
  | None => []
  | Some values =>
      phase1_surface_observe_recursive_grouping_generic_param
        (phase1_generic_params_kind_type_spine_first values) ::
      map phase1_surface_observe_recursive_grouping_generic_param
        (phase1_generic_params_kind_type_spine_rest values)
  end.

Definition phase1_surface_observe_recursive_grouping_requirements
  (requirements : option Phase1SurfaceGenericRequirementsRecursiveGroupingSpine)
  : list nat :=
  match requirements with
  | None => []
  | Some values =>
      map phase1_surface_generic_requirement_recursive_grouping_spine_index
        (phase1_generic_requirements_recursive_grouping_spine_entries values)
  end.

Definition phase1_surface_observe_recursive_grouping_fields
  (fields : option Phase1SurfaceFieldTypeListSpine) : list string :=
  match fields with
  | None => []
  | Some values =>
      phase1_field_type_spine_name
        (phase1_field_type_list_spine_first values) ::
      map phase1_field_type_spine_name
        (phase1_field_type_list_spine_rest values)
  end.

Definition phase1_surface_observe_recursive_grouping_tuple_arity
  (types : option Phase1SurfaceTupleTypeListSpine) : nat :=
  match types with
  | None => 0
  | Some values => S (length (phase1_tuple_type_list_spine_rest values))
  end.

Definition phase1_surface_observe_recursive_grouping_variant
  (variant : Phase1SurfaceRecordFieldTypeVariantSpine)
  : Phase1SurfaceRecursiveGroupingObservedVariant :=
  {| phase1_observed_variant_name :=
       phase1_record_field_type_variant_spine_name variant;
     phase1_observed_variant_payload :=
       match phase1_record_field_type_variant_spine_payload variant with
       | None => Phase1ObservedNoPayload
       | Some (Phase1RecordFieldTypeVariantRecordPayloadSpine fields) =>
           Phase1ObservedRecordPayload
             (phase1_surface_observe_recursive_grouping_fields fields)
       | Some (Phase1RecordFieldTypeVariantTuplePayloadSpine types) =>
           Phase1ObservedTuplePayload
             (phase1_surface_observe_recursive_grouping_tuple_arity types)
       end |}.

Definition phase1_surface_observe_recursive_grouping_record_data
  (refined : Phase1SurfaceRecursiveGroupingImplementationRecordDataDeclaration)
  : Phase1SurfaceRecursiveGroupingObservedRecordData :=
  match refined with
  | Phase1RecursiveGroupingImplementationRecordDeclaration record =>
      Phase1ObservedRecord
        (phase1_recursive_grouping_impl_record_name record)
        (phase1_surface_observe_recursive_grouping_generic_params
          (phase1_recursive_grouping_impl_record_generic_params record))
        (phase1_recursive_grouping_impl_record_mode record)
        (phase1_surface_observe_recursive_grouping_requirements
          (phase1_recursive_grouping_impl_record_requirements record))
        (phase1_surface_observe_recursive_grouping_fields
          (phase1_recursive_grouping_impl_record_fields record))
  | Phase1RecursiveGroupingImplementationDataDeclaration data_value =>
      Phase1ObservedData
        (phase1_recursive_grouping_impl_data_name data_value)
        (phase1_surface_observe_recursive_grouping_generic_params
          (phase1_recursive_grouping_impl_data_generic_params data_value))
        (phase1_recursive_grouping_impl_data_mode data_value)
        (phase1_surface_observe_recursive_grouping_requirements
          (phase1_recursive_grouping_impl_data_requirements data_value))
        (phase1_surface_observe_recursive_grouping_variant
          (phase1_recursive_grouping_impl_data_first_variant data_value) ::
         map phase1_surface_observe_recursive_grouping_variant
          (phase1_recursive_grouping_impl_data_rest_variants data_value))
  end.

Definition phase1_surface_recursive_grouping_observed_tag
  (observed : Phase1SurfaceRecursiveGroupingObservedRecordData)
  : Phase1SurfaceDeclarationTag :=
  match observed with
  | Phase1ObservedRecord _ _ _ _ _ => Phase1RecordDeclaration
  | Phase1ObservedData _ _ _ _ _ => Phase1DataDeclaration
  end.

Theorem phase1_surface_recursive_grouping_observation_admitted_tag_exact :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    phase1_surface_recursive_grouping_observed_tag
      (phase1_surface_observe_recursive_grouping_record_data refined) =
    phase1_declaration_spine_tag declaration.
Proof.
  intros declaration refined Hnormalize.
  pose proof
    (phase1_surface_recursive_grouping_implementation_tagged_round_trip
      declaration refined Hnormalize) as Hkey.
  rewrite <- Hkey.
  destruct refined; reflexivity.
Qed.

Theorem phase1_surface_recursive_grouping_observation_admitted_key_sound :
  forall declaration refined,
    phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
      declaration = Some refined ->
    exists observed,
      observed = phase1_surface_observe_recursive_grouping_record_data refined /\
      phase1_surface_recursive_grouping_observed_tag observed =
        phase1_declaration_spine_tag declaration /\
      phase1_surface_recursive_grouping_implementation_declaration_spine
        refined = declaration.
Proof.
  intros declaration refined Hnormalize.
  exists (phase1_surface_observe_recursive_grouping_record_data refined).
  split; [reflexivity |].
  split.
  - exact
      (phase1_surface_recursive_grouping_observation_admitted_tag_exact
        declaration refined Hnormalize).
  - exact
      (phase1_surface_recursive_grouping_implementation_tagged_round_trip
        declaration refined Hnormalize).
Qed.

Example phase1_surface_recursive_grouping_observation_absent_empty_collapse :
  phase1_surface_observe_recursive_grouping_record_data
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_absent_requirements_record) =
  phase1_surface_observe_recursive_grouping_record_data
    (Phase1RecursiveGroupingImplementationRecordDeclaration
      phase1_surface_impl_present_empty_requirements_record).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example phase1_surface_recursive_grouping_observation_admitted_keys_not_collapsed :
  Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_absent_requirements_record <>
  Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_present_empty_requirements_record.
Proof.
  intro Hequal.
  apply phase1_surface_impl_absent_and_present_empty_are_distinct.
  exact
    (f_equal phase1_surface_recursive_grouping_implementation_record_data_tree
      Hequal).
Qed.

Example phase1_surface_recursive_grouping_observation_absent_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_absent_requirements_record)) =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_absent_requirements_record).
Proof.
  exact phase1_surface_accepted_key_absent_requirements_stable.
Qed.

Example phase1_surface_recursive_grouping_observation_empty_accepted :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    (phase1_surface_recursive_grouping_implementation_declaration_spine
      (Phase1RecursiveGroupingImplementationRecordDeclaration
        phase1_surface_impl_present_empty_requirements_record)) =
  Some (Phase1RecursiveGroupingImplementationRecordDeclaration
    phase1_surface_impl_present_empty_requirements_record).
Proof.
  exact phase1_surface_accepted_key_present_empty_requirements_stable.
Qed.

Example phase1_surface_recursive_grouping_observation_malformed_literal_rejected :
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine
    {| phase1_declaration_spine_tag := Phase1RecordDeclaration;
       phase1_declaration_spine_selected_tree := PTLiteral "Nat" |} = None.
Proof.
  exact phase1_surface_impl_literal_under_record_tag_rejected.
Qed.
