# Phase 1 implementation notes

This directory contains checker-, proof-, provider-, and Systems-facing records produced as Phase 1 implementation slices landed.

## Status ownership

Most `*-v1.md` files here are **historical slice records**, not continuously rewritten roadmaps. Their positive semantic claims describe the slice they accompanied, but statements such as “not yet,” “deferred,” or “this slice does not claim” describe the repository state at that point in history and may later become obsolete.

Current Phase 1 status is owned by the project **Logic Ledger** at claim level and the **Conformance Matrix** at case level. In the repository, checked proof/certification artifacts and executable conformance/correspondence tests are authoritative evidence over prose status summaries.

The important exceptions are documents that explicitly declare themselves current normative authorities, especially:

- [`surface-grammar-v1.md`](surface-grammar-v1.md), together with [`../../grammar/phase1-surface.ebnf`](../../grammar/phase1-surface.ebnf), for the Phase 1 concrete-syntax epoch; and
- any document whose own text explicitly states that it is a current normative specification rather than an implementation-slice record.

## Reading historical slices

A historical slice document should therefore be read as:

1. the semantic boundary implemented or exercised by that slice;
2. the cases and artifacts that accompanied it; and
3. a timestamped record of what was deliberately outside that slice at the time.

Do not infer from an old “not yet” list that the named later slice is still open. Do not infer from a historical implementation note that its implementation is the language specification. Phil’s accepted ADRs/contracts, current logic ledger, conformance matrix, and checked repository evidence retain those roles.
