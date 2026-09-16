From Stdlib Require Import Extraction.

From Phil.Surface Require Import GrammarParserProductionKernel.

Extraction Language Haskell.

(* Reuse the repository's established native container mappings.  Rocq string
   and ascii deliberately remain in their generated representation in this
   staging slice; the production bridge will encode Haskell Text as exact UTF-8
   bytes rather than pretending Unicode Text is definitionally Rocq string. *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "SurfaceGrammarRecognizerKernel"
  phase1_surface_reference_parse
  phase1_surface_reference_accepts.
