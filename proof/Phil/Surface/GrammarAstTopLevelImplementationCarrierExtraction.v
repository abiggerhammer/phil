From Stdlib Require Import Extraction.

From Phil.Surface Require Import GrammarAstTopLevelImplementationCarrier.

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "SurfaceGrammarAstTopLevelCarrierKernel"
  phase1_surface_make_implementation_attribute
  phase1_surface_make_implementation_top_level.
