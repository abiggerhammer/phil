From Stdlib Require Import Extraction.

From Phil.Surface Require Import GrammarAstImplementationRepresentation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "SurfaceGrammarAstRepresentationKernel"
  phase1_surface_name_list_to_implementation
  phase1_surface_name_list_from_implementation
  phase1_surface_optional_name_list_to_implementation
  phase1_surface_optional_name_list_from_implementation
  phase1_surface_import_header_to_implementation
  phase1_surface_import_header_from_implementation
  phase1_surface_import_headers_from_implementation
  phase1_surface_source_header_to_implementation
  phase1_surface_source_header_from_implementation.
