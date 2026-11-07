# Phase 1 implementation notes

This directory contains checker-, proof-, provider-, and Systems-facing records produced as Phase 1 implementation slices landed.

## Status ownership

Most `*-v1.md` files here are **historical slice records**, not continuously rewritten roadmaps. Their positive semantic claims describe the slice they accompanied, but statements such as “not yet,” “deferred,” or “this slice does not claim” describe the repository state at that point in history and may later become obsolete.

Current Phase 1 status is owned by the project **Logic Ledger** at claim level and the **Conformance Matrix** at case level. In the repository, checked proof/certification artifacts and executable conformance/correspondence tests are authoritative evidence over prose status summaries.

The important exceptions are documents that explicitly declare themselves current normative authorities, especially:

- [`surface-grammar-v1.md`](surface-grammar-v1.md), together with [`../../grammar/phase1-surface.ebnf`](../../grammar/phase1-surface.ebnf), for the Phase 1 concrete-syntax epoch; and
- any document whose own text explicitly states that it is a current normative specification rather than an implementation-slice record.

## CI operational safety

- [PR-head workflow supersession policy](pr-head-ci-supersession-policy-v1.md) — bounded migration of the highest-traffic PR checks to cancellation-safe concurrency groups, with automated guard tests and explicit exceptions for main/release and coordination workflows.

## Entry points for formal-methods review

- [Normative Phase 1 surface EBNF](../../grammar/phase1-surface.ebnf) — authoritative concrete syntax and token forms; successful parsing is not semantic acceptance.
- [Grammar-v1 status, lexical rules and versioning policy](surface-grammar-v1.md) — defines the concrete-syntax authority boundary and derivation of proof-facing grammar artifacts.
- [Syntax–semantics completeness audit](syntax-semantics-completeness-v1.md) — reconciles programmer-expressible choices against the accepted Phase 1 contracts; it does not independently make typing rules normative.
- [Phase 1 typing and semantics reader's guide](typing-and-semantics-reader-guide-v1.md) — non-normative map of existing semantic authorities, models and proof-scope caveats.
- [Three worked typing-rule families](typing-rules-worked-examples-draft-v1.md) — illustrative positive/expected-negative examples; not all negatives are executable conformance witnesses yet.
- [Formal-semantics judgment inventory (FSEM-00)](formal-semantics-judgment-inventory-v0.md) — proposed rule interfaces, translation boundaries and explicit outstanding evidence, tracked in [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
- [FSEM-01 proposed loan-state correspondence](formal-semantics-loan-state-correspondence-fsem01-v0.md) — exact source binder/production resource identities, an explicit candidate Rocq relation, and undischarged source-to-model proof obligations (non-normative).
- [FSEM-01 executable production loan-state trace](formal-semantics-loan-transition-trace-fsem01-v1.md) — same checker transitions, exact live-owner/loan checkpoints and escaped-view error-prefix tests; not a source-to-Rocq theorem.
- [FSEM-01 first Rocq loan-transition proof slice](formal-semantics-exact-loan-transition-model-fsem01-v1.md) — conditional identity-preserving linear loan start/end proofs and explicit unproved Haskell/source encoding boundaries.
- [FSEM-01 binder-name encoding proof and production Text checks](formal-semantics-binder-name-encoding-fsem01-v1.md) — ASCII-string injectivity theorem with Haskell canonical codec tests; Unicode/Text representation and declaration-ID bridges remain explicit.
- [FSEM-01 bounded declaration-root representation](formal-semantics-declaration-identity-bridge-fsem01-v1.md) — duplicate-free finite catalog relation between normalized declaration IDs and actual Haskell root keys; catalog stability and Unicode refinement remain explicit.
- [FSEM-01 represented production loan-state checkpoints](formal-semantics-represented-loan-trace-fsem01-v1.md) — model start/close/terminal and rejected-prefix proofs, plus source-derived production trace ↔ bounded catalog identity and membership tests; no universal Haskell refinement.
- [FSEM-01 bounded transition and BorrowEscape error bridge](formal-semantics-step-error-bridge-fsem01-v1.md) — fail-closed model steps, no post-rejection successors, and actual production trace tampering tests; cross-language simulation still open.
- [FSEM-01 versioned source observation and checked wire decoder](formal-semantics-observation-wire-fsem01-v1.md) — deterministic, source-SHA256-bound actual checker artifacts uploaded by CI and evaluated byte-for-byte by a Rocq-proved decoder; producer refinement still open.
- [FSEM-01 bounded source-observation simulation](formal-semantics-source-simulation-fsem01-v1.md) — conditional Rocq replay with exact producer-binding and finite catalog premises, plus CI witnesses over real source-derived artifacts; no universal Haskell refinement.
- [FSEM-01 bounded observation producer-fidelity proof](formal-semantics-producer-fidelity-fsem01-v1.md) — by-construction preservation of all source-run artifact fields and injective snapshot encoding, with checker-state extraction still a tested trust boundary.
- [FSEM-01 checker-state resource observation bridge](formal-semantics-checker-state-observation-fsem01-v1.md) — exact observed one-owner Haskell Map/Set flags, Rocq resource-context lookup lemmas and start/end/return correspondence; cross-language state refinement remains open.
- [FSEM-01 full bounded resource-context wire](formal-semantics-resource-context-wire-fsem01-v1.md) — exact four-map/set checkpoint extraction, real Haskell start/end/consume transition replay, Rocq-decoded full-state evidence; universal cross-language refinement still open.
- [FSEM-01 two-owner Core frame and context2 wire](formal-semantics-two-owner-context-fsem01-v1.md) — separate source-resolved owner identities, real two-owner Haskell Core operations, independent versioned wire and Rocq frame lemmas; full two-owner source elaboration remains open.
- [FSEM-01 direct two-linear-owner source conformance](formal-semantics-two-owner-source-fsem01-v1.md) — real two-parameter function with exact production map/loan observations; opaque tuple return and general elaboration still open.

These review documents do not replace accepted semantic contracts, the normative grammar, the Logic Ledger, or exact-commit proof and conformance results.

## Reading historical slices

A historical slice document should therefore be read as:

1. the semantic boundary implemented or exercised by that slice;
2. the cases and artifacts that accompanied it; and
3. a timestamped record of what was deliberately outside that slice at the time.

Do not infer from an old “not yet” list that the named later slice is still open. Do not infer from a historical implementation note that its implementation is the language specification. Phil’s accepted ADRs/contracts, current logic ledger, conformance matrix, and checked repository evidence retain those roles.
