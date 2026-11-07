# Phase 1 implementation notes

This directory contains checker-, proof-, provider-, and Systems-facing records produced as Phase 1 implementation slices landed.

## Status ownership

Most `*-v1.md` files here are **historical slice records**, not continuously rewritten roadmaps. Their positive semantic claims describe the slice they accompanied, but statements such as “not yet,” “deferred,” or “this slice does not claim” describe the repository state at that point in history and may later become obsolete.

Current Phase 1 status is owned by the project **Logic Ledger** at claim level and the **Conformance Matrix** at case level. In the repository, checked proof/certification artifacts and executable conformance/correspondence tests are authoritative evidence over prose status summaries.

The important exceptions are documents that explicitly declare themselves current normative authorities, especially:

- [`surface-grammar-v1.md`](surface-grammar-v1.md), together with [`../../grammar/phase1-surface.ebnf`](../../grammar/phase1-surface.ebnf), for the Phase 1 concrete-syntax epoch; and
- any document whose own text explicitly states that it is a current normative specification rather than an implementation-slice record.

## Entry points for formal-methods review

- [Phase 1 typing and semantics reader's guide](typing-and-semantics-reader-guide-v1.md) — non-normative map of existing semantic authorities, models and proof-scope caveats.
- [Three worked typing-rule families](typing-rules-worked-examples-draft-v1.md) — illustrative positive/expected-negative examples; not all negatives are executable conformance witnesses yet.
- [Formal-semantics judgment inventory (FSEM-00)](formal-semantics-judgment-inventory-v0.md) — proposed rule interfaces, translation boundaries and explicit outstanding evidence, tracked in [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
- [FSEM-01 proposed loan-state correspondence](formal-semantics-loan-state-correspondence-fsem01-v0.md) — exact source binder/production resource identities, an explicit candidate Rocq relation, and undischarged source-to-model proof obligations (non-normative).
- [FSEM-01 executable production loan-state trace](formal-semantics-loan-transition-trace-fsem01-v1.md) — same checker transitions, exact live-owner/loan checkpoints and escaped-view error-prefix tests; not a source-to-Rocq theorem.
- [FSEM-01 first Rocq loan-transition proof slice](formal-semantics-exact-loan-transition-model-fsem01-v1.md) — conditional identity-preserving linear loan start/end proofs and explicit unproved Haskell/source encoding boundaries.

These review documents do not replace accepted semantic contracts, the normative grammar, the Logic Ledger, or exact-commit proof and conformance results.

## Reading historical slices

A historical slice document should therefore be read as:

1. the semantic boundary implemented or exercised by that slice;
2. the cases and artifacts that accompanied it; and
3. a timestamped record of what was deliberately outside that slice at the time.

Do not infer from an old “not yet” list that the named later slice is still open. Do not infer from a historical implementation note that its implementation is the language specification. Phil’s accepted ADRs/contracts, current logic ledger, conformance matrix, and checked repository evidence retain those roles.
