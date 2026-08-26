From Corelib Require Extraction.
From Phil.Core Require Import
  CallableRefinementImplementation
  CallableRefinementImplementationBridge.

Extraction Language Haskell.

(* Keep the extracted kernel on ordinary Haskell Bool/list representations so
   the production adapter does not need a second handwritten structural
   translation layer between Data.Set domains and the proved incidence kernel. *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].

Extraction "CallableRefinementKernel"
  incidenceVector
  vectorSubsetb
  decideCallableRefinement.
