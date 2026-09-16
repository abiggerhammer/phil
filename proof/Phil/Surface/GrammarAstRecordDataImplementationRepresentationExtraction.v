From Stdlib Require Import Extraction.

From Phil.Surface Require Import
  GrammarAstRecordDataImplementationRepresentation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extraction "SurfaceGrammarAstRecordDataRepresentationKernel"
  phase1_surface_record_to_implementation
  phase1_surface_record_from_implementation
  phase1_surface_data_to_implementation
  phase1_surface_data_from_implementation
  phase1_surface_normalize_record_data_declaration_spine.
