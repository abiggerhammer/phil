# Phase 1 surface parser AST effect correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #891.

The preceding converse-side slices establish the certified source spine, declaration choice, type-alias shell, generic parameters and requirements, static-reference/static-value structure, recursive type payloads, ordinary expression structure, and proposition structure. The next shared unresolved payload is `effect_set_expression`.

This slice closes the reusable effect-set layer:

- exact `effect_set_expression` choice between a brace-delimited literal and a static-reference expression;
- empty and nonempty effect-set literals with source order preserved;
- exact effect-label static-reference spines;
- optional term arguments on each effect expression;
- full ordinary expression correspondence for effect arguments through #889, including the explicit command-family boundary; and
- exact effect-set payloads for `effects E within ...` generic requirements, replacing #881's previous tag-only evidence for that payload.

Static references continue to use #883's established shallow static-argument correspondence: exact qualified names and static-argument grammar categories are preserved, while recursively nested static-argument payloads remain a later mutual-recursion seam. This slice does not silently strengthen that boundary.

## Evidence boundary

Session expressions remain untranslated. Command-expression family identity is exact, but the 27 command payload bodies remain opaque through #889. Remaining declaration bodies have not yet been totally translated.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted. The next high-leverage shared slice is session-expression structure; after session/effect payloads are closed, the remaining command and declaration families can reuse the accumulated translators.