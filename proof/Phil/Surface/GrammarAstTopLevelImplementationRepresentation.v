From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstImplementationRepresentation
  GrammarAstTopLevelSpine
  GrammarAstTopLevelTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Implementation-facing representation bridge for the proof-complete
  top-level/declaration spine of PHIL-SURFACE-GRAMMAR-CORR-001.

  #939/#960 already isolate and bind the source-header representation.  This
  layer deliberately leaves that exact extracted kernel unchanged.  It adds a
  separate carrier for the next proof-complete layer: top-level attributes and
  the closed fifteen-way declaration tag.

  Declaration-family bodies remain explicit certified ParseTree payload holes.
  The implementation-facing view does not inspect, encode, or pretend to
  refine those payloads; exact retained payload trees are supplied separately
  when reconstructing the proof-side top-level spine.
*)

Record Phase1SurfaceImplementationAttribute : Type := {
  phase1_impl_attribute_name : string;
  phase1_impl_attribute_value : string
}.

Record Phase1SurfaceImplementationTopLevel : Type := {
  phase1_impl_top_level_attributes : list Phase1SurfaceImplementationAttribute;
  phase1_impl_top_level_declaration_tag : Phase1SurfaceDeclarationTag
}.

Definition phase1_surface_attribute_to_implementation
  (attribute : Phase1SurfaceAttributeSpine)
  : Phase1SurfaceImplementationAttribute :=
  {| phase1_impl_attribute_name := phase1_attribute_spine_name attribute;
     phase1_impl_attribute_value := phase1_attribute_spine_value attribute |}.

Definition phase1_surface_attribute_from_implementation
  (attribute : Phase1SurfaceImplementationAttribute)
  : Phase1SurfaceAttributeSpine :=
  {| phase1_attribute_spine_name := phase1_impl_attribute_name attribute;
     phase1_attribute_spine_value := phase1_impl_attribute_value attribute |}.

Theorem phase1_surface_attribute_implementation_round_trip :
  forall attribute,
    phase1_surface_attribute_from_implementation
      (phase1_surface_attribute_to_implementation attribute) = attribute.
Proof.
  intros [name value].
  reflexivity.
Qed.

Theorem phase1_surface_attributes_implementation_round_trip :
  forall attributes,
    map phase1_surface_attribute_from_implementation
      (map phase1_surface_attribute_to_implementation attributes) = attributes.
Proof.
  intros attributes.
  induction attributes as [|attribute rest IH].
  - reflexivity.
  - cbn.
    rewrite phase1_surface_attribute_implementation_round_trip.
    rewrite IH.
    reflexivity.
Qed.

Definition phase1_surface_top_level_to_implementation
  (top_level : Phase1SurfaceTopLevelSpine)
  : Phase1SurfaceImplementationTopLevel :=
  {| phase1_impl_top_level_attributes :=
       map phase1_surface_attribute_to_implementation
         (phase1_top_level_spine_attributes top_level);
     phase1_impl_top_level_declaration_tag :=
       phase1_declaration_spine_tag
         (phase1_top_level_spine_declaration top_level) |}.

Definition phase1_surface_top_level_selected_tree
  (top_level : Phase1SurfaceTopLevelSpine) : GrammarDerivation.ParseTree :=
  phase1_declaration_spine_selected_tree
    (phase1_top_level_spine_declaration top_level).

Definition phase1_surface_top_level_from_implementation
  (top_level : Phase1SurfaceImplementationTopLevel)
  (selected_tree : GrammarDerivation.ParseTree)
  : Phase1SurfaceTopLevelSpine :=
  {| phase1_top_level_spine_attributes :=
       map phase1_surface_attribute_from_implementation
         (phase1_impl_top_level_attributes top_level);
     phase1_top_level_spine_declaration :=
       {| phase1_declaration_spine_tag :=
            phase1_impl_top_level_declaration_tag top_level;
          phase1_declaration_spine_selected_tree := selected_tree |} |}.

Theorem phase1_surface_top_level_implementation_round_trip :
  forall top_level,
    phase1_surface_top_level_from_implementation
      (phase1_surface_top_level_to_implementation top_level)
      (phase1_surface_top_level_selected_tree top_level) = top_level.
Proof.
  intros [attributes [tag selected_tree]].
  unfold phase1_surface_top_level_from_implementation.
  unfold phase1_surface_top_level_to_implementation.
  unfold phase1_surface_top_level_selected_tree.
  f_equal.
  apply phase1_surface_attributes_implementation_round_trip.
Qed.

Fixpoint phase1_surface_top_levels_from_implementation
  (top_levels : list Phase1SurfaceImplementationTopLevel)
  (selected_trees : list GrammarDerivation.ParseTree)
  : option (list Phase1SurfaceTopLevelSpine) :=
  match top_levels, selected_trees with
  | [], [] => Some []
  | top_level :: rest, selected_tree :: selected_rest =>
      match
        phase1_surface_top_levels_from_implementation rest selected_rest
      with
      | Some reconstructed =>
          Some
            (phase1_surface_top_level_from_implementation
              top_level selected_tree :: reconstructed)
      | None => None
      end
  | _, _ => None
  end.

Theorem phase1_surface_top_levels_implementation_round_trip :
  forall top_levels,
    phase1_surface_top_levels_from_implementation
      (map phase1_surface_top_level_to_implementation top_levels)
      (map phase1_surface_top_level_selected_tree top_levels) =
      Some top_levels.
Proof.
  intros top_levels.
  induction top_levels as [|top_level rest IH].
  - reflexivity.
  - cbn.
    rewrite IH.
    rewrite phase1_surface_top_level_implementation_round_trip.
    reflexivity.
Qed.

Definition phase1_surface_source_top_level_as_header
  (source : Phase1SurfaceSourceTopLevel) : Phase1SurfaceSourceHeader :=
  {| phase1_source_header_module := phase1_source_top_level_module source;
     phase1_source_header_imports := phase1_source_top_level_imports source;
     phase1_source_header_top_levels :=
       map phase1_surface_top_level_spine_tree
         (phase1_source_top_level_declarations source) |}.

Theorem phase1_surface_source_top_level_header_tree_agrees :
  forall source,
    phase1_surface_source_header_tree
      (phase1_surface_source_top_level_as_header source) =
    phase1_surface_source_top_level_tree source.
Proof.
  intros [module_name imports top_levels].
  reflexivity.
Qed.

Definition phase1_surface_source_top_level_header_implementation
  (source : Phase1SurfaceSourceTopLevel)
  : Phase1SurfaceImplementationSourceHeader :=
  phase1_surface_source_header_to_implementation
    (phase1_surface_source_top_level_as_header source).

Definition phase1_surface_source_top_levels_implementation
  (source : Phase1SurfaceSourceTopLevel)
  : list Phase1SurfaceImplementationTopLevel :=
  map phase1_surface_top_level_to_implementation
    (phase1_source_top_level_declarations source).

Theorem phase1_surface_source_top_level_count_agrees_with_header :
  forall source,
    phase1_impl_source_top_level_count
      (phase1_surface_source_top_level_header_implementation source) =
    List.length (phase1_surface_source_top_levels_implementation source).
Proof.
  intros [module_name imports top_levels].
  unfold phase1_surface_source_top_level_header_implementation,
    phase1_surface_source_top_levels_implementation,
    phase1_surface_source_top_level_as_header,
    phase1_surface_source_header_to_implementation.
  cbn.
  repeat rewrite map_length.
  reflexivity.
Qed.

Theorem phase1_surface_certified_source_top_levels_have_implementation_view :
  forall tokens tree,
    GrammarDerivation.Phase1CompleteDerivation tokens tree ->
    exists source,
      phase1_surface_normalize_source_top_level_tree tree = Some source /\
      phase1_surface_source_top_level_tree source = tree /\
      phase1_surface_top_levels_from_implementation
        (phase1_surface_source_top_levels_implementation source)
        (map phase1_surface_top_level_selected_tree
          (phase1_source_top_level_declarations source)) =
        Some (phase1_source_top_level_declarations source) /\
      phase1_impl_source_top_level_count
        (phase1_surface_source_top_level_header_implementation source) =
      List.length (phase1_surface_source_top_levels_implementation source).
Proof.
  intros tokens tree Hcomplete.
  destruct
    (phase1_surface_normalize_source_top_level_total tokens tree Hcomplete)
    as [source [Hnormalize Htree]].
  exists source.
  repeat split.
  - exact Hnormalize.
  - exact Htree.
  - unfold phase1_surface_source_top_levels_implementation.
    apply phase1_surface_top_levels_implementation_round_trip.
  - apply phase1_surface_source_top_level_count_agrees_with_header.
Qed.
