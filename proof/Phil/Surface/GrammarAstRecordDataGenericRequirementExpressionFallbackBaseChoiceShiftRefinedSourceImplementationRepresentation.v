From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelImplementationRepresentation
  GrammarAstRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSourceReference.

Import ListNotations.
Open Scope string_scope.

(*
  Lift the whole-source shift-refined record/data carrier into the existing
  implementation-facing module/import/attribute representations.

  The declaration payload remains the already-refined Rocq record/data carrier;
  this slice only removes the remaining proof-side header and top-level
  attribute representation seams.  The resulting implementation view is
  lossless on every value produced from the certified carrier and is tied
  directly to the reference-parser soundness/finite-fuel results from #1511.

  Structural Rocq surface correspondence only.  This does not extract a Haskell
  kernel, bind the production AST, add other declaration families, change
  Grammar-v1, or alter runtime/evaluation behavior.  Continues
  PHIL-SURFACE-GRAMMAR-CORR-001 after #1511.
*)

Record
  Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationTopLevel
  : Type := {
  phase1_shift_refined_record_data_impl_top_level_attributes :
    list Phase1SurfaceImplementationAttribute;
  phase1_shift_refined_record_data_impl_top_level_declaration :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedDeclaration
}.

Definition
  phase1_surface_shift_refined_record_data_top_level_to_implementation
  (top_level :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine)
  : Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationTopLevel :=
  {| phase1_shift_refined_record_data_impl_top_level_attributes :=
       map phase1_surface_attribute_to_implementation
         (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes
           top_level);
     phase1_shift_refined_record_data_impl_top_level_declaration :=
       phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration
         top_level |}.

Definition
  phase1_surface_shift_refined_record_data_top_level_from_implementation
  (top_level :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationTopLevel)
  : Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedTopLevelSpine :=
  {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_attributes :=
       map phase1_surface_attribute_from_implementation
         (phase1_shift_refined_record_data_impl_top_level_attributes top_level);
     phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_top_level_declaration :=
       phase1_shift_refined_record_data_impl_top_level_declaration top_level |}.

Theorem
  phase1_surface_shift_refined_record_data_top_level_implementation_round_trip :
  forall top_level,
    phase1_surface_shift_refined_record_data_top_level_from_implementation
      (phase1_surface_shift_refined_record_data_top_level_to_implementation
        top_level) =
    top_level.
Proof.
  intros [attributes declaration].
  unfold
    phase1_surface_shift_refined_record_data_top_level_from_implementation,
    phase1_surface_shift_refined_record_data_top_level_to_implementation.
  cbn.
  rewrite phase1_surface_attributes_implementation_round_trip.
  reflexivity.
Qed.

Theorem
  phase1_surface_shift_refined_record_data_top_levels_implementation_round_trip :
  forall top_levels,
    map phase1_surface_shift_refined_record_data_top_level_from_implementation
      (map
        phase1_surface_shift_refined_record_data_top_level_to_implementation
        top_levels) =
    top_levels.
Proof.
  intros top_levels.
  induction top_levels as [|top_level rest IH].
  - reflexivity.
  - cbn.
    rewrite
      phase1_surface_shift_refined_record_data_top_level_implementation_round_trip.
    rewrite IH.
    reflexivity.
Qed.

Record
  Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource
  : Type := {
  phase1_shift_refined_record_data_impl_source_module :
    option (list string);
  phase1_shift_refined_record_data_impl_source_imports :
    list Phase1SurfaceImplementationImportHeader;
  phase1_shift_refined_record_data_impl_source_declarations :
    list
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationTopLevel
}.

Definition
  phase1_surface_shift_refined_record_data_source_to_implementation
  (source :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource)
  : Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource :=
  {| phase1_shift_refined_record_data_impl_source_module :=
       phase1_surface_optional_name_list_to_implementation
         (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module
           source);
     phase1_shift_refined_record_data_impl_source_imports :=
       map phase1_surface_import_header_to_implementation
         (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports
           source);
     phase1_shift_refined_record_data_impl_source_declarations :=
       map
         phase1_surface_shift_refined_record_data_top_level_to_implementation
         (phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations
           source) |}.

Definition
  phase1_surface_shift_refined_record_data_source_from_implementation
  (source :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource)
  : option
      Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSource :=
  match
    phase1_surface_optional_name_list_from_implementation
      (phase1_shift_refined_record_data_impl_source_module source),
    phase1_surface_import_headers_from_implementation
      (phase1_shift_refined_record_data_impl_source_imports source)
  with
  | Some module_name, Some imports =>
      Some
        {| phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_module :=
             module_name;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_imports :=
             imports;
           phase1_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_declarations :=
             map
               phase1_surface_shift_refined_record_data_top_level_from_implementation
               (phase1_shift_refined_record_data_impl_source_declarations
                 source) |}
  | _, _ => None
  end.

Theorem
  phase1_surface_shift_refined_record_data_source_implementation_round_trip :
  forall source,
    phase1_surface_shift_refined_record_data_source_from_implementation
      (phase1_surface_shift_refined_record_data_source_to_implementation source) =
    Some source.
Proof.
  intros [module_name imports declarations].
  unfold
    phase1_surface_shift_refined_record_data_source_from_implementation,
    phase1_surface_shift_refined_record_data_source_to_implementation.
  cbn.
  rewrite phase1_surface_optional_name_list_implementation_round_trip.
  rewrite phase1_surface_import_headers_implementation_round_trip.
  rewrite
    phase1_surface_shift_refined_record_data_top_levels_implementation_round_trip.
  reflexivity.
Qed.

Definition
  phase1_surface_shift_refined_record_data_implementation_source_tree
  (source :
    Phase1SurfaceRecordDataGenericRequirementExpressionFallbackBaseChoiceShiftRefinedImplementationSource)
  : option ParseTree :=
  match phase1_surface_shift_refined_record_data_source_from_implementation source
  with
  | Some refined =>
      Some
        (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
          refined)
  | None => None
  end.

Theorem
  phase1_surface_shift_refined_record_data_implementation_source_tree_round_trip :
  forall source,
    phase1_surface_shift_refined_record_data_implementation_source_tree
      (phase1_surface_shift_refined_record_data_source_to_implementation source) =
    Some
      (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
        source).
Proof.
  intros source.
  unfold
    phase1_surface_shift_refined_record_data_implementation_source_tree.
  rewrite
    phase1_surface_shift_refined_record_data_source_implementation_round_trip.
  reflexivity.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_source_fuel_has_implementation_view :
  forall fuel tokens refined,
    phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
      fuel tokens = Some refined ->
    exists implementation,
      implementation =
        phase1_surface_shift_refined_record_data_source_to_implementation
          refined /\
      phase1_surface_shift_refined_record_data_implementation_source_tree
        implementation =
        Some
          (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
            refined) /\
      phase1_surface_reference_parse tokens =
        Some
          ([],
           ResultTree
             (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
               refined)) /\
      Phase1CompleteDerivation tokens
        (phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
          refined).
Proof.
  intros fuel tokens refined Hreference.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_sound
      fuel tokens refined Hreference)
    as [source [tree [Hsource [Hnormalize [Htree [Hparse Hcomplete]]]]]].
  exists
    (phase1_surface_shift_refined_record_data_source_to_implementation refined).
  repeat split.
  - reflexivity.
  - apply
      phase1_surface_shift_refined_record_data_implementation_source_tree_round_trip.
  - rewrite Htree.
    exact Hparse.
  - rewrite Htree.
    exact Hcomplete.
Qed.

Theorem
  phase1_surface_reference_shift_refined_record_data_source_derivable_has_implementation_view :
  forall tokens source,
    phase1_surface_reference_source_top_level tokens = Some source ->
    phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_derivable
      source ->
    exists fuel refined implementation,
      phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel
        fuel tokens = Some refined /\
      implementation =
        phase1_surface_shift_refined_record_data_source_to_implementation
          refined /\
      phase1_surface_shift_refined_record_data_source_from_implementation
        implementation = Some refined /\
      phase1_surface_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_tree
        refined =
      phase1_surface_source_top_level_tree source.
Proof.
  intros tokens source Hsource Hderive.
  destruct
    (phase1_surface_reference_record_data_generic_requirement_expression_fallback_base_choice_shift_refined_source_fuel_total
      tokens source Hsource Hderive)
    as [fuel [refined [Hreference Htree]]].
  exists fuel, refined,
    (phase1_surface_shift_refined_record_data_source_to_implementation refined).
  repeat split.
  - exact Hreference.
  - reflexivity.
  - apply
      phase1_surface_shift_refined_record_data_source_implementation_round_trip.
  - exact Htree.
Qed.
