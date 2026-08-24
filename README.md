# Phil

**Phil is a systems language in which architecture is executable and implementation is replaceable.**

Phil is part of the broader Logics to Order research program. It starts from system boundaries, protocols, authority, and proof obligations, then lowers those meanings toward executable implementations without making one implementation the definition of the system.

## Start here

New to Phil? Read **[A Tour of Phil — Phase 0](docs/tutorials/tour-phase0.md)**. It follows the frozen Phase 0 upload program from its client/server conversation through recognition, validation, evidence, ownership, native execution, and certification, while defining the terminology as it goes.

The Tour is intentionally scoped to the Phase 0 reference program. Phase 0 demonstrates one architecture end to end; Phase 1 generalizes that machinery into a language for architectures.

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

Phase 0 is complete as a design snapshot. The executable implementation now spans the resource/session/recognition kernel, deterministic focusing and checked decision certificates, whole-component surface checking, Systems IR and verification, Assurance manifests and proof certificates, and explicit LLVM/runtime lowering slices through the current Phase 0 protocol frontier.

The exact implemented/non-goal boundary is maintained in `docs/implementation-status.md`. The current proof-certification state is summarized separately in `docs/phase-0/assurance-status.md`; the checked proof corpus and mechanically verified assurance artifacts remain authoritative over prose summaries.

## Repository map

- `src/Phil/Core/` — executable Phil Core checker kernel
- `src/Phil/Surface/` — location-preserving parser, elaborator, and whole-component checker
- `src/Phil/Systems/` — explicit Systems IR, lowering decisions, and verifier
- `src/Phil/Assurance/` — content-bound assurance ledger, manifest, and proof-certificate machinery
- `src/Phil/LLVM/` — explicit LLVM IR/lowering and target-specific verification
- `proof/Phil/` — Rocq proof corpus
- `app/` — checker, certification, and bootstrap executables
- `test/` — conformance and correspondence tests
- `docs/tutorials/tour-phase0.md` — beginner-facing tour of the frozen Phase 0 reference program
- `docs/implementation-status.md` — implemented vs. still-open checker surface
- `docs/phase-0/assurance-status.md` — current Phase 0 proof-certification snapshot
- `docs/phase-0/` — checker-facing Phase 0 design/ABI snapshot imported from the durable research corpus
- `examples/upload/` — successful upload demonstrator source sketches
- `examples/rejected/` — semantically rejected Phase 0 source witnesses

The complete Phase 0 design corpus remains in the durable research archive while it is migrated into Git history. For live implementation and checked proof state, this repository is intended to become the source of truth.

## Build

The implementation is a Cabal package:

```sh
cabal build all
cabal test all
cabal run phil-core
```

The surface parser can also be exercised directly:

```sh
cabal run phil-core -- parse examples/upload/client.phil
```

A successful `parse` command still means only syntactic acceptance and source-location recovery; semantic acceptance belongs to whole-component checking and later competent lowering/verification stages.

## Naming

- Language: **Phil**
- Source extension: `.phil`
- Logical kernel: **Phil Core**
- `Phil` is a proper name, not an acronym or backronym.

Tool names beyond the bootstrap executable remain provisional.
