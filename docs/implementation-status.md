# Phil Core implementation status

This file tracks the executable checker against the accepted Phase 0 Core judgments. It is intentionally stricter than a conventional roadmap: an item is either implemented in the checker, represented only as a design document, or not started.

## Implemented in the bootstrap slice

- `Γ` unrestricted bindings remain reusable.
- `A` affine bindings may be consumed at most once.
- `Δ` linear bindings are consumed exactly once along complete continuing paths.
- Shared-loan state is checker bookkeeping attached to owners in `A` or `Δ`, not a fourth structural zone.
- An owner cannot be consumed while a shared loan is live.
- A loan must end before the owner can be consumed.
- Continuing branch joins require identical linear residue.
- Affine residue is conservatively forgotten when a capability is absent from any continuing branch.
- Complete-component checks can reject leftover linear resources and escaping loans.
- Obligation IDs are unique within a checking state; re-emitting the identical obligation is idempotent, while reusing an ID for a different obligation is rejected.

## Next checker slices

1. Session-head representation and endpoint progression for `!`, `?`, `⊕`, `&`, and `end[o]`.
2. Process/control outcomes: `Continue`, `Return`, `Closed`, and `Failed`, including terminal-path linear-resource rules.
3. Grammar-backed receive with `PendingRecv`, scoped raw-byte loans, recognition, and commit.
4. Bidirectional value checking and explicit definitional/propositional equality boundary.
5. Refinements, evidence matching, explicit transport, and stable residual obligation generation.
6. Deterministic focusing/elaboration rules.
7. Parser and surface-to-Core elaboration.
8. Conformance harness over the accepted/rejected `.phil` corpus.
9. Assurance-ledger handoff and manifest verification.

## Explicit non-goals of the first commit

The bootstrap does not claim source-level Phil conformance yet. In particular it does not parse Phil syntax, project dependent session types, solve refinements, validate the upload protocol, or lower to systems/LLVM IR. Those claims would be premature until the corresponding checker competence exists.
