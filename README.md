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

Phase 0 is complete as a design snapshot. The executable implementation has grown from the original resource kernel through sessions, recognition, refinements/evidence, focusing, checked decision certificates, obligation disposition, and now the first trusted Phil source front end.

The exact implemented/non-goal boundary is maintained in `docs/implementation-status.md`. The parser now accepts the accepted upload witnesses and all twenty intentionally rejected Phase 0 programs as syntax; semantic rejection remains assigned to the competent later checker layer.

## Repository map

- `src/Phil/Core/` — executable Phil Core checker kernel
- `src/Phil/Surface/` — location-preserving Phase 0 parser and deterministic fragment elaborator
- `app/` — checker/bootstrap executable and parse-only CLI entry point
- `test/` — conformance tests for the implemented checker/front-end slices
- `docs/implementation-status.md` — implemented vs. still-open checker surface
- `docs/phase-0/` — checker-facing Phase 0 snapshot imported from the durable research corpus
- `examples/upload/` — successful upload demonstrator source sketches
- `examples/rejected/` — semantically rejected Phase 0 source witnesses

The complete Phase 0 design corpus remains in the durable research archive while it is migrated into Git history. For live implementation state, this repository is intended to become the source of truth.

## Build

The implementation is a Cabal package:

```sh
cabal build all
cabal test all
cabal run phil-core
```

The trusted surface parser can be exercised directly without claiming semantic acceptance:

```sh
cabal run phil-core -- parse examples/upload/client.phil
```

A successful `parse` command means only that the complete input is syntactically valid Phil and that source locations were recorded. Whole-component semantic checking of parsed source is the next slice.

## Naming

- Language: **Phil**
- Source extension: `.phil`
- Logical kernel: **Phil Core**
- `Phil` is a proper name, not an acronym or backronym.

Tool names beyond the bootstrap executable remain provisional.
