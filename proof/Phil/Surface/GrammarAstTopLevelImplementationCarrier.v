From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstTopLevelImplementationRepresentation.

Import ListNotations.

(*
  Compact extraction boundary for production binding of the proof-complete
  top-level representation staged by #964.

  This file does not introduce a second semantic representation.  It exposes
  constructor functions for the already-defined implementation carrier so the
  production Haskell boundary can depend on a small exact extracted ABI rather
  than the full proof-side ParseTree dependency closure.
*)

Definition phase1_surface_make_implementation_attribute
  (name value : string)
  : Phase1SurfaceImplementationAttribute :=
  {| phase1_impl_attribute_name := name;
     phase1_impl_attribute_value := value |}.

Definition phase1_surface_make_implementation_top_level
  (attributes : list Phase1SurfaceImplementationAttribute)
  (tag : Phase1SurfaceDeclarationTag)
  : Phase1SurfaceImplementationTopLevel :=
  {| phase1_impl_top_level_attributes := attributes;
     phase1_impl_top_level_declaration_tag := tag |}.

Theorem phase1_surface_attribute_to_implementation_uses_carrier :
  forall attribute,
    phase1_surface_attribute_to_implementation attribute =
    phase1_surface_make_implementation_attribute
      (phase1_attribute_spine_name attribute)
      (phase1_attribute_spine_value attribute).
Proof.
  intros [name value].
  reflexivity.
Qed.

Theorem phase1_surface_top_level_to_implementation_uses_carrier :
  forall top_level,
    phase1_surface_top_level_to_implementation top_level =
    phase1_surface_make_implementation_top_level
      (map phase1_surface_attribute_to_implementation
        (phase1_top_level_spine_attributes top_level))
      (phase1_declaration_spine_tag
        (phase1_top_level_spine_declaration top_level)).
Proof.
  intros [attributes declaration].
  reflexivity.
Qed.
