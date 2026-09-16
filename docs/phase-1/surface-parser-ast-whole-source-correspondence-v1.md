# Phase 1 Grammar-v1 whole-source AST correspondence

This slice composes the correspondence chain accumulated through #914 into one span-insensitive whole-source carrier.

The certified path starts from the extracted Grammar-v1 reference parse tree. The production path starts from `GrammarV1SourceFile`. Both are projected into the same `GrammarV1ReferenceSourceCore`, preserving in one ordered value:

- optional module identity;
- ordered imports and optional import selections;
- ordered top-level attributes;
- the exact one-of-fifteen declaration-family choice; and
- the complete family-specific declaration body for every Grammar-v1 declaration alternative.

The declaration dispatch is explicit and fail closed. `ReferenceAstTopLevel` supplies the independently decoded declaration tag, and the selected family translator must accept the same declaration body. There is no reflection over `Show`, source spelling, file position, or Haskell constructor names. The production side uses the corresponding independent top-level tag and family translator in the same way.

The family payloads are not reimplemented here. The whole-source layer reuses the direct correspondence authorities landed for record/data, type-alias/claim, callable contracts, provider declarations, capability/boundary declarations, function/component declarations, protocols, and architecture/program declarations, together with the recursively closed expression, proposition, effect, session, command, type, and static-argument layers beneath them.

The permanent gate strictly compiles this cumulative composition and compares every accepted manifest fixture through the certified recognizer and production parser as one complete source value. Direct controls additionally exercise module/import/attribute composition, declaration ordering, Unicode source structure, and an adversarial same-family body drift.

## Evidence boundary

This closes the previously disconnected **whole-source composition seam** and demonstrates cumulative executable correspondence over the complete maintained corpus. It is the final `Tested` integration audit for the current Haskell certified-tree/production-AST bridge.

It does **not** by itself establish the stronger universal implementation-refinement claim required by `PHIL-ASSURE-IMPL-CORR-001`. Corpus equality, even after all Grammar-v1 families are covered, is not a proof that every certified-valid reference tree translates to the production representation or that the production AST builder is mechanically equivalent to an extracted certified translation.

Accordingly this slice does not promote the parser implementation to `Implementation Refined`. The remaining proof successor is a universal/mechanical correspondence: define or expose the proof-side normalized AST translation, prove its totality/correctness for every certified complete Grammar-v1 parse, and mechanically connect that result to the production representation with the required round-trip/refinement property.
