# Phil — Phase 0 Groundwork

Private working package for the Logics to Order / Means of Production research program.

**Working language name:** **Phil**

## Project statement

**What Phil is**

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**

**How Phil works**

> **Phil constructs software top-down from boundaries, protocols, and obligations.**

**How Phil is used**

> **Prototype → verify → rewrite → certify.**

**What Phil does about cost**

> **Phil makes the cost of assurance explicit and erases assurance machinery that has completed its work.**

**How Phil assigns cost**

> **Proof should cost at compile time; uncertainty should cost at runtime.**

Together, these describe Phil as a systems language viewed from the highest semantic level. It begins with the structure and responsibilities of a whole system, lowers those meanings into executable implementations, and retains runtime assurance work only where execution still depends on runtime facts that cannot be discharged statically.

Phil is a proper name, not an acronym or backronym. The name is provisional through the early design and implementation phases, but the documents and examples use it consistently so that we can find out whether it fits the language in practice.

This package begins Phase 0: semantic decisions, demonstrator design, trust boundaries, and a corpus of Phil programs that must be accepted or rejected before implementation begins.

## Provisional naming conventions

- Language: **Phil**
- Source files: `.phil`
- Repository/package stem: `phil`
- Compiler/checker command: `phil` or `philc` — not yet settled
- Formatter: `philfmt` — provisional
- Language server: `phil-lsp` — provisional
- Logical kernel: **Phil Core**

Only the language name and `.phil` source extension are used normatively in this Phase 0 package. Tool names remain open until implementation makes the command structure clearer.

## Contents

- `docs/phase-0-plan.md` — ordered work plan and exit criteria
- `docs/glossary.md` — shared Phil vocabulary
- `docs/naming.md` — rationale and provisional naming conventions
- `docs/tcb.md` — initial trusted-computing-base statement
- `docs/adr/` — eleven architecture decision records
- `docs/semantics/core-judgments.md` — normative provider/bidirectional Phase 0 Core checking judgments
- `docs/semantics/upload-protocol.md` — accepted demonstrator semantics
- `docs/semantics/upload-traces.md` — expected observable traces
- `docs/semantics/upload-failure-resource-matrix.md` — normative failure/resource transitions
- `docs/semantics/upload-session-types.md` — projected dependent client/server session types
- `docs/semantics/structural-mode-matrix.md` — normative Phase 0 ownership/mode classifications
- `docs/semantics/refinement-obligation-matrix.md` — normative Phase 0 refinement/evidence classifications and discharge mechanisms
- `docs/semantics/upload-assurance-ledger.md` — normative upload assurance-manifest / evidence-graph witness
- `docs/semantics/assurance-ledger-invalid-cases.md` — negative conformance cases for ledger/manifest verification
- `docs/semantics/upload-runtime-cost-plan.md` — normative runtime representation/cost plan for checked-runtime and certified-release profiles
- `docs/semantics/runtime-cost-invalid-cases.md` — negative conformance cases for runtime representation and cost attribution
- `docs/semantics/upload-ir-stage-contracts.md` — normative property-directed IR competence/lowering witness
- `docs/semantics/ir-lowering-invalid-cases.md` — negative conformance cases for cross-stage lowering preservation
- `docs/semantics/upload-llvm-emission-contract.md` — normative backend/target-to-LLVM emission witness
- `docs/semantics/llvm-boundary-invalid-cases.md` — negative conformance cases for LLVM assumptions/emission
- `examples/upload/client.phil` and `server.phil` — role-local successful Phil sketches
- `examples/upload/wire/` — valid and malformed frame-payload byte fixtures
- `examples/rejected/` — negative Phil corpus

## Current status

The framed-upload boundary is frozen. All eleven Phase 0 ADRs—ADR-009, ADR-004, ADR-005, ADR-003, ADR-002, ADR-006, ADR-001, ADR-010, ADR-011, ADR-007, and ADR-008—are **Accepted**.

Together they now fix:

- the binary demonstrator protocol;
- recognition versus contextual validation;
- typed failure, fatal termination, cancellation, and cleanup;
- the dependent binary session calculus and recognition-gated endpoint progression;
- the unrestricted/affine/linear structural discipline and scoped shared-loan semantics;
- the restricted refinement/evidence language, named residual obligations, and explicit static/runtime discharge boundary;
- the provider-oriented semantic foundation, executable bidirectional residual checker interface, session polarity, focusing discipline, and definitional/propositional equality boundary;
- the append-only assurance/evidence graph, assumption nodes, obligation revisions, manifest closure rules, and cross-ledger handoff to runtime/lowering decisions;
- the runtime representation/erasure discipline, checked-runtime versus certified-release profiles, semantic-versus-conservative cost attribution, and systems-IR representation responsibilities;
- the property-directed IR competence layers, fact-transfer rule, stage contracts, systems/backend boundary, and cross-stage preservation obligations;
- the LLVM emission/trust boundary, evidence-backed optimizer promises, poison/UB discipline, artifact-scoped toolchain assumptions, and first translation-validation target.

The ordered Phase 0 ADR review is complete. ADR-008 fixes the final Phil-aware handoff: pre-optimization LLVM is produced under an explicit stage contract; optimized LLVM and native artifacts add separately scoped toolchain transformations and assurance dependencies.

## Immediate next implementation artifact

The next implementation artifact is a tiny executable Phil Core checker implementing the accepted `Σ ; Γ ; A ; Δ` / bidirectional residual semantics and the demonstrator conformance corpus.

The checker may stop at Core or the protocol/boundary layer; systems/LLVM lowering is a separate implementation track governed by ADR-007/008. The Phase 0 design no longer contains an unresolved semantic decision blocking checker implementation.
