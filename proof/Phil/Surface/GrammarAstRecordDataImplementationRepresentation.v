From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstRecordFieldsSpine
  GrammarAstRecordFieldsTotality
  GrammarAstVariantPayloadSpine
  GrammarAstDataTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Implementation-facing representation bridge for the proof-complete record
  and data declaration payloads of PHIL-SURFACE-GRAMMAR-CORR-001.

  #964/#983 bind the top-level attribute/declaration-family surface while
  retaining each declaration body as an exact ParseTree payload hole.  The
  record/data proof tranche has now descended through the complete shared
  outer structure: names, generic parameters, structural mode, generic
  requirements, record fields, data variants, and variant payload shape.

  This layer replaces the whole-body hole for those two declaration families
  with extracted carriers isomorphic to the proof-complete spines.  Nested
  recursive payloads that their own proof layers still retain as ParseTree
  values (generic-kind type payloads, requirement payloads, field types, and
  tuple-variant type expressions) remain explicit holes here as well.  No
  deeper correspondence is claimed by this staging slice.
*)

Record Phase1SurfaceImplementationRecordDeclaration : Type := {
  phase1_impl_record_name : string;
  phase1_impl_record_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_impl_record_mode : option Phase1SurfaceStructuralMode;
  phase1_impl_record_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_impl_record_fields : option Phase1SurfaceFieldListSpine
}.

Record Phase1SurfaceImplementationDataDeclaration : Type := {
  phase1_impl_data_name : string;
  phase1_impl_data_generic_params : option Phase1SurfaceGenericParamsSpine;
  phase1_impl_data_mode : option Phase1SurfaceStructuralMode;
  phase1_impl_data_requirements : option Phase1SurfaceGenericRequirementsSpine;
  phase1_impl_data_first_variant : Phase1SurfaceVariantPayloadVariantSpine;
  phase1_impl_data_rest_variants : list Phase1SurfaceVariantPayloadVariantSpine
}.

Inductive Phase1SurfaceImplementationRecordDataDeclaration : Type :=
| Phase1ImplementationRecordDeclaration
    (record : Phase1SurfaceImplementationRecordDeclaration)
| Phase1ImplementationDataDeclaration
    (data_value : Phase1SurfaceImplementationDataDeclaration).

Definition phase1_surface_record_to_implementation
  (record : Phase1SurfaceRecordFieldsSpine)
  : Phase1SurfaceImplementationRecordDeclaration :=
  {| phase1_impl_record_name := phase1_record_fields_spine_name record;
     phase1_impl_record_generic_params :=
       phase1_record_fields_spine_generic_params record;
     phase1_impl_record_mode := phase1_record_fields_spine_mode record;
     phase1_impl_record_requirements :=
       phase1_record_fields_spine_requirements record;
     phase1_impl_record_fields := phase1_record_fields_spine_fields record |}.

Definition phase1_surface_record_from_implementation
  (record : Phase1SurfaceImplementationRecordDeclaration)
  : Phase1SurfaceRecordFieldsSpine :=
  {| phase1_record_fields_spine_name := phase1_impl_record_name record;
     phase1_record_fields_spine_generic_params :=
       phase1_impl_record_generic_params record;
     phase1_record_fields_spine_mode := phase1_impl_record_mode record;
     phase1_record_fields_spine_requirements :=
       phase1_impl_record_requirements record;
     phase1_record_fields_spine_fields := phase1_impl_record_fields record |}.

Theorem phase1_surface_record_implementation_round_trip :
  forall record,
    phase1_surface_record_from_implementation
      (phase1_surface_record_to_implementation record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Theorem phase1_surface_record_implementation_inverse :
  forall record,
    phase1_surface_record_to_implementation
      (phase1_surface_record_from_implementation record) = record.
Proof.
  intros [name generic_params mode requirements fields].
  reflexivity.
Qed.

Definition phase1_surface_data_to_implementation
  (data_value : Phase1SurfaceDataVariantPayloadSpine)
  : Phase1SurfaceImplementationDataDeclaration :=
  {| phase1_impl_data_name := phase1_data_variant_payload_spine_name data_value;
     phase1_impl_data_generic_params :=
       phase1_data_variant_payload_spine_generic_params data_value;
     phase1_impl_data_mode := phase1_data_variant_payload_spine_mode data_value;
     phase1_impl_data_requirements :=
       phase1_data_variant_payload_spine_requirements data_value;
     phase1_impl_data_first_variant :=
       phase1_data_variant_payload_spine_first_variant data_value;
     phase1_impl_data_rest_variants :=
       phase1_data_variant_payload_spine_rest_variants data_value |}.

Definition phase1_surface_data_from_implementation
  (data_value : Phase1SurfaceImplementationDataDeclaration)
  : Phase1SurfaceDataVariantPayloadSpine :=
  {| phase1_data_variant_payload_spine_name := phase1_impl_data_name data_value;
     phase1_data_variant_payload_spine_generic_params :=
       phase1_impl_data_generic_params data_value;
     phase1_data_variant_payload_spine_mode := phase1_impl_data_mode data_value;
     phase1_data_variant_payload_spine_requirements :=
       phase1_impl_data_requirements data_value;
     phase1_data_variant_payload_spine_first_variant :=
       phase1_impl_data_first_variant data_value;
     phase1_data_variant_payload_spine_rest_variants :=
       phase1_impl_data_rest_variants data_value |}.

Theorem phase1_surface_data_implementation_round_trip :
  forall data_value,
    phase1_surface_data_from_implementation
      (phase1_surface_data_to_implementation data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Theorem phase1_surface_data_implementation_inverse :
  forall data_value,
    phase1_surface_data_to_implementation
      (phase1_surface_data_from_implementation data_value) = data_value.
Proof.
  intros [name generic_params mode requirements first_variant rest_variants].
  reflexivity.
Qed.

Definition phase1_surface_implementation_record_tree
  (record : Phase1SurfaceImplementationRecordDeclaration) : ParseTree :=
  phase1_surface_record_fields_spine_tree
    (phase1_surface_record_from_implementation record).

Definition phase1_surface_implementation_data_tree
  (data_value : Phase1SurfaceImplementationDataDeclaration) : ParseTree :=
  phase1_surface_data_variant_payload_spine_tree
    (phase1_surface_data_from_implementation data_value).

Definition phase1_surface_implementation_record_data_tree
  (declaration : Phase1SurfaceImplementationRecordDataDeclaration) : ParseTree :=
  match declaration with
  | Phase1ImplementationRecordDeclaration record =>
      phase1_surface_implementation_record_tree record
  | Phase1ImplementationDataDeclaration data_value =>
      phase1_surface_implementation_data_tree data_value
  end.

Definition phase1_surface_normalize_record_implementation
  (tree : ParseTree) : option Phase1SurfaceImplementationRecordDeclaration :=
  match phase1_surface_normalize_record_fields_tree tree with
  | Some record => Some (phase1_surface_record_to_implementation record)
  | None => None
  end.

Theorem phase1_surface_normalize_record_implementation_round_trip :
  forall tree record,
    phase1_surface_normalize_record_implementation tree = Some record ->
    phase1_surface_implementation_record_tree record = tree.
Proof.
  intros tree record Hnormalize.
  unfold phase1_surface_normalize_record_implementation in Hnormalize.
  destruct (phase1_surface_normalize_record_fields_tree tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst record.
  unfold phase1_surface_implementation_record_tree.
  rewrite phase1_surface_record_implementation_round_trip.
  eapply phase1_surface_normalize_record_fields_tree_round_trip.
  exact Hrefined.
Qed.

Definition phase1_surface_normalize_data_implementation
  (tree : ParseTree) : option Phase1SurfaceImplementationDataDeclaration :=
  match phase1_surface_normalize_data_variant_payload_tree tree with
  | Some data_value => Some (phase1_surface_data_to_implementation data_value)
  | None => None
  end.

Theorem phase1_surface_normalize_data_implementation_round_trip :
  forall tree data_value,
    phase1_surface_normalize_data_implementation tree = Some data_value ->
    phase1_surface_implementation_data_tree data_value = tree.
Proof.
  intros tree data_value Hnormalize.
  unfold phase1_surface_normalize_data_implementation in Hnormalize.
  destruct (phase1_surface_normalize_data_variant_payload_tree tree)
    as [refined |] eqn:Hrefined; try discriminate Hnormalize.
  inversion Hnormalize; subst data_value.
  unfold phase1_surface_implementation_data_tree.
  rewrite phase1_surface_data_implementation_round_trip.
  eapply phase1_surface_normalize_data_variant_payload_tree_round_trip.
  exact Hrefined.
Qed.

Definition phase1_surface_normalize_record_data_declaration_spine
  (declaration : Phase1SurfaceDeclarationSpine)
  : option Phase1SurfaceImplementationRecordDataDeclaration :=
  match phase1_declaration_spine_tag declaration with
  | Phase1RecordDeclaration =>
      match phase1_surface_normalize_record_implementation
              (phase1_declaration_spine_selected_tree declaration) with
      | Some record => Some (Phase1ImplementationRecordDeclaration record)
      | None => None
      end
  | Phase1DataDeclaration =>
      match phase1_surface_normalize_data_implementation
              (phase1_declaration_spine_selected_tree declaration) with
      | Some data_value => Some (Phase1ImplementationDataDeclaration data_value)
      | None => None
      end
  | _ => None
  end.

Theorem phase1_surface_normalize_record_data_declaration_spine_round_trip :
  forall declaration refined,
    phase1_surface_normalize_record_data_declaration_spine declaration =
      Some refined ->
    phase1_surface_implementation_record_data_tree refined =
      phase1_declaration_spine_selected_tree declaration.
Proof.
  intros [tag selected_tree] refined Hnormalize.
  destruct tag; cbn in Hnormalize; try discriminate Hnormalize.
  - destruct (phase1_surface_normalize_record_implementation selected_tree)
      as [record |] eqn:Hrecord; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply phase1_surface_normalize_record_implementation_round_trip.
    exact Hrecord.
  - destruct (phase1_surface_normalize_data_implementation selected_tree)
      as [data_value |] eqn:Hdata; try discriminate Hnormalize.
    inversion Hnormalize; subst refined.
    cbn.
    eapply phase1_surface_normalize_data_implementation_round_trip.
    exact Hdata.
Qed.

Theorem phase1_surface_certified_record_has_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "record_decl")
      input rest tree ->
    exists record,
      phase1_surface_normalize_record_implementation tree = Some record /\
      phase1_surface_implementation_record_tree record = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_record_fields_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists (phase1_surface_record_to_implementation refined).
  split.
  - unfold phase1_surface_normalize_record_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_implementation_record_tree.
    rewrite phase1_surface_record_implementation_round_trip.
    exact Htree.
Qed.

Theorem phase1_surface_certified_data_has_implementation_view :
  forall path input rest tree,
    Derives phase1_surface_rules path (ENonterminal "data_decl")
      input rest tree ->
    exists data_value,
      phase1_surface_normalize_data_implementation tree = Some data_value /\
      phase1_surface_implementation_data_tree data_value = tree.
Proof.
  intros path input rest tree Hderive.
  destruct
    (phase1_surface_normalize_data_variant_payload_tree_total_from_derivation
      path input rest tree Hderive)
    as [refined [Hnormalize Htree]].
  exists (phase1_surface_data_to_implementation refined).
  split.
  - unfold phase1_surface_normalize_data_implementation.
    rewrite Hnormalize.
    reflexivity.
  - unfold phase1_surface_implementation_data_tree.
    rewrite phase1_surface_data_implementation_round_trip.
    exact Htree.
Qed.
