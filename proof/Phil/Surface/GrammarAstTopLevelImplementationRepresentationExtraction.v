From Stdlib Require Import Extraction.

From Phil.Surface Require Import GrammarAstTopLevelImplementationRepresentation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "SurfaceGrammarAstTopLevelRepresentationKernel"
  phase1_surface_attribute_to_implementation
  phase1_surface_attribute_from_implementation
  phase1_surface_top_level_to_implementation
  phase1_surface_top_level_selected_tree
  phase1_surface_top_level_from_implementation
  phase1_surface_top_levels_from_implementation
  phase1_surface_source_top_level_header_implementation
  phase1_surface_source_top_levels_implementation.
