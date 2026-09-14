From Stdlib Require Import Extraction.

From Phil.Surface Require Import
  SurfaceRecordDataProductionCarrier.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive unit => "()" [ "()" ].

Extraction "SurfaceGrammarAstRecordDataCarrierKernel"
  phase1_surface_make_production_generic_param
  phase1_surface_make_production_record_payload
  phase1_surface_make_production_tuple_payload
  phase1_surface_make_production_variant
  phase1_surface_make_production_record
  phase1_surface_make_production_data.
