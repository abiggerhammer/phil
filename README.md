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

Phase 0 is frozen as the first complete design/execution snapshot. Phase 1 is active and is removing the witness-specific assumptions: the repository now contains generalized architecture identity and instantiation, structural generics, first-class callable/effect and authority machinery, provider qualification, a witness-neutral Systems/StageContract stack through explicit staging-effect accounting, the normative Phase 1 Surface Grammar v1, and the first production checker whose acceptance path is mechanically refined against its Rocq semantics.

The canonical Phase 1 source front end, remaining representation/deployment-profile hooks, broader implementation-refinement work, and the full ordinary-source upload/Steve exit witnesses are still in progress. `docs/implementation-status.md` is therefore a **Phase 0 bootstrap-checker status snapshot**, not the global Phase 1 roadmap. For current claims, prefer the checked proof/certification artifacts, Phase 1 conformance tests, and the corresponding `docs/phase-1/` slice records; human-facing project status is maintained in the Phase 1 Logic Ledger and Conformance Matrix.

## Repository map

- `src/Phil/Core/` — executable Phil Core checker kernel
- `src/Phil/Surface/` — location-preserving parser, elaborator, and whole-component checker
- `src/Phil/Systems/` — explicit Systems IR, lowering decisions, and verifier
- `src/Phil/Assurance/` — content-bound assurance ledger, manifest, and proof-certificate machinery
- `src/Phil/LLVM/` — explicit LLVM IR/lowering and target-specific verification
- `grammar/phase1-surface.ebnf` — sole normative Phase 1 concrete-syntax authority
- `proof/Phil/` — Rocq proof corpus
- `app/` — checker, certification, and bootstrap executables
- `test/` — conformance and correspondence tests
- `docs/tutorials/tour-phase0.md` — beginner-facing tour of the frozen Phase 0 reference program
- `docs/implementation-status.md` — Phase 0 bootstrap-checker status snapshot
- `docs/phase-0/assurance-status.md` — Phase 0 proof-certification snapshot
- `docs/phase-0/` — checker-facing frozen Phase 0 design/ABI snapshot
- `docs/phase-1/surface-grammar-v1.md` — Phase 1 concrete-syntax conventions and grammar-version policy
- `docs/phase-1/` — Phase 1 implementation/conformance slice records
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

## License

Phil's source code, proofs, examples, and repository documentation are licensed under the **Apache License 2.0**. See [`LICENSE`](LICENSE).

Project names, logos, mascots, and other visual identity assets are not granted additional trademark or branding rights by the software license.

## Naming

- Language: **Phil**
- Source extension: `.phil`
- Logical kernel: **Phil Core**
- `Phil` is a proper name, not an acronym or backronym.

Tool names beyond the bootstrap executable remain provisional.
