# Architecture import implementation refinement v1

This note stages mechanical implementation refinement for Certified `PHIL-ARCH-IMPORT-001` without changing production.

## Certified semantic seam

The Certified import model says that import resolution may make an already-checked `DeclarationIdentity` available under one local spelling. It does not grant capability authority, satisfy provider requirements, accept assumptions, discharge obligations, instantiate architecture occurrences, choose realizations, or create runtime effects.

After module/export lookup has selected a checked declaration identity, the semantic binding gate is:

1. a selected export must exist;
2. the requested local name must be fresh; and
3. success preserves the exact local spelling and exact declaration identity.

The module locator is intentionally not semantic once the same checked declaration identity has been selected.

## Extracted staging kernel

`proof/Phil/Surface/ImportNoninterferenceImplementation.v` defines:

- `decideImportResolutionByFacts`, whose inputs are only selected-export presence and local-name freshness;
- `planImportedBinding`, which preserves exactly the local spelling and declaration identity.

`proof/Phil/Surface/ImportNoninterferenceImplementationExtraction.v` extracts those functions as `ArchitectureImportKernel.hs`.

The direct correspondence harness checks acceptance, unknown-export precedence, duplicate-local-name rejection, and exact binding-plan construction.

## Native bridge boundary

This staging slice does **not** move these facts into Rocq:

- concrete `Text` equality;
- `Data.Map` membership/insertion/traversal and `ImportAll` ordering;
- module-table lookup and module/export provenance;
- construction and truth of the selected `DeclarationIdentity`;
- package/version solving or repository provenance;
- Haskell runtime/toolchain behavior.

Production `src/Phil/Surface/Check.hs` remains unchanged in this staging PR. A green staging run therefore leaves `PHIL-ARCH-IMPORT-001` at `Discharged / Certified`; a separate closeout must check in the exact extracted kernel and route production binding acceptance/construction through it before the ledger can move to `Implementation Refined`.
