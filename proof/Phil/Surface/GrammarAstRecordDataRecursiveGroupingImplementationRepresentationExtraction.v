From Stdlib Require Import Extraction.

From Phil.Surface Require Import
  GrammarAstRecordDataRecursiveGroupingImplementationRepresentation.

(* Extract precisely the bounded, tree-preserving record/data carrier bridge.
   This is not a production Haskell parser binding or a whole-source proof. *)
Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].

Extraction "SurfaceGrammarAstRecordDataRecursiveGroupingKernel"
  phase1_surface_recursive_grouping_record_to_implementation
  phase1_surface_recursive_grouping_record_from_implementation
  phase1_surface_recursive_grouping_data_to_implementation
  phase1_surface_recursive_grouping_data_from_implementation
  phase1_surface_recursive_grouping_implementation_record_tree
  phase1_surface_recursive_grouping_implementation_data_tree
  phase1_surface_recursive_grouping_implementation_record_data_tree
  phase1_surface_normalize_recursive_grouping_record_implementation
  phase1_surface_normalize_recursive_grouping_data_implementation
  phase1_surface_normalize_recursive_grouping_record_data_declaration_spine.
