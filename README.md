# Phil

**Phil is a systems language in which architecture is executable and implementation is replaceable.**

Phil is part of the broader Logics to Order research program. It starts from system boundaries, protocols, authority, and proof obligations, then lowers those meanings toward executable implementations without making one implementation the definition of the system.

## Core formulations

**What Phil is**

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**

**How Phil works**

> **Phil constructs software top-down from boundaries, protocols, and obligations.**

**Development model**

> **Prototype → verify → rewrite → certify.**

**Assurance cost**

> **Phil makes the cost of assurance explicit and erases assurance machinery that has completed its work.**

**Cost placement**

> **Proof should cost at compile time; uncertainty should cost at runtime.**

## Current implementation slice

Phase 0 is complete as a design snapshot. The first executable implementation target is a small Phil Core checker over the accepted residual-resource contexts:

```text
Σ ; Γ ; A ; Δ
```

This repository begins with the resource kernel that later checking judgments depend on:

- unrestricted (`Γ`), affine (`A`), and linear (`Δ`) bindings;
- exact affine/linear consumption;
- scoped shared loans over affine and linear owners;
- continuing-branch residue joins;
- detection of unconsumed linear resources;
- stable obligation IDs and conflict detection.

The parser, surface elaborator, session-head rules, recognition/validation boundary, refinement discharge, assurance-ledger verifier, and lowering pipeline are intentionally not faked in the bootstrap commit. They will be added against the accepted Phase 0 semantics.

## Repository map

- `src/Phil/Core/` — executable checker kernel
- `app/` — tiny checker bootstrap executable
- `test/` — conformance tests for the implemented kernel slice
- `docs/implementation-status.md` — implemented vs. still-open checker surface
- `docs/phase-0/` — checker-facing Phase 0 snapshot imported from the durable research corpus
- `examples/upload/` — successful upload demonstrator source sketches

The complete Phase 0 design corpus remains in the durable research archive while it is migrated into Git history. For live implementation state, this repository is intended to become the source of truth.

## Build

The bootstrap is a Cabal package:

```sh
cabal build all
cabal test all
cabal run phil-core
```

The package currently has no parser and does not accept `.phil` source on stdin. `phil-core` is a smoke-test executable for the Core resource kernel.

## Naming

- Language: **Phil**
- Source extension: `.phil`
- Logical kernel: **Phil Core**
- `Phil` is a proper name, not an acronym or backronym.

Tool names beyond the bootstrap executable remain provisional.
