# Phase 1 surface parser Rocq source-spine correspondence v1

This slice begins the universal/mechanical successor to the completed Haskell whole-source correspondence audit in #916.

The production-side audit now compares the certified Grammar-v1 parse tree and the production AST as one complete source value, but that remains **Tested** evidence. The implementation-refinement ledger requires a proof-side executable translation and a mechanical connection to the production representation rather than finite corpus equality alone.

## What this slice adds

`GrammarAstSourceSpine.v` introduces the first proof-side normalized source carrier:

- optional module declaration subtree;
- ordered import declaration subtrees; and
- ordered top-level declaration subtrees.

The carrier intentionally stops at those subtrees. It does not yet duplicate the 15 declaration-family payload definitions in Rocq. That keeps the first proof seam narrow and lets later slices refine the already-isolated subtrees family by family.

`phase1_surface_normalize_source_spine` accepts only the exact outer Grammar-v1 tree shape:

```text
source_file = [ module_decl ], { import_decl }, { top_level_decl }
```

It also requires the root nonterminal name to be the generated `phase1_surface_start`.

`phase1_surface_source_spine_tree` reconstructs the exact outer tree shape from the normalized carrier. The theorem

`phase1_surface_normalize_source_spine_round_trip`

proves that every successful normalization is lossless at this boundary: reconstruction returns the original certified parse tree exactly.

The production-kernel binding

`phase1_surface_reference_source_spine`

runs the already-certified total reference parser and immediately applies the proof-side source-spine normalizer. The theorem

`phase1_surface_reference_source_spine_sound`

proves universally that every returned source spine comes from a successful certified complete Grammar-v1 parse, reconstructs that exact parse tree, and therefore corresponds to a `Phase1CompleteDerivation`.

## Evidence boundary

This slice is **not** the totality theorem yet. In particular, it does not yet prove that every `Phase1CompleteDerivation` or every successful certified parse must be accepted by `phase1_surface_normalize_source_spine`.

The immediate successor is therefore:

1. prove source-spine normalization total for every certified complete Grammar-v1 parse;
2. refine module/import/top-level subtrees into proof-side normalized values;
3. prove those refinements total and structurally faithful;
4. extract the normalized translation; and
5. mechanically connect the extracted carrier to the production AST representation with the ledger-required refinement/round-trip property.

Until that chain is complete, `PHIL-SURFACE-GRAMMAR-CORR-001` remains open and `PHIL-ASSURE-IMPL-CORR-001` must not be promoted to Implementation Refined.
