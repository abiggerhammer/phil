From Stdlib Require Import Extraction.

From Phil.Surface Require Import
  GrammarAstRecordDataExpressionOuterImplementationRepresentation.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].

Extraction "SurfaceGrammarAstRecordDataExpressionOuterRepresentationKernel"
  phase1_surface_expression_outer_record_to_implementation
  phase1_surface_expression_outer_record_from_implementation
  phase1_surface_expression_outer_data_to_implementation
  phase1_surface_expression_outer_data_from_implementation
  phase1_surface_normalize_expression_outer_record_data_declaration_spine.
