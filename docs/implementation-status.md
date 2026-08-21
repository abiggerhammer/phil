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

## Implemented in the session-progression slice

- Session heads represent `!`, `?`, `⊕`, `&`, `end[o]`, guarded recursion, and recursion variables.
- `⊕`/`&` branches carry an optional payload binder/type as required by ADR-003 rather than only a label and continuation.
- A successful structural session step consumes the current linear endpoint and creates at most one explicitly fresh successor endpoint at the declared continuation.
- Send and receive expose their declared message binder/type to the next checker layer.
- Internal selection and external offer reject the wrong polarity and reject undeclared labels.
- Branch selection exposes the branch payload specification and exact continuation.
- Declared close consumes an `end[o]` endpoint only when the requested outcome exactly matches.
- Guarded recursive heads are unfolded only enough to expose a communication head; unguarded self-recursion and unbound session variables are rejected.
- Structural duality is executable and involutive over the represented session forms.

The session step API is deliberately **not** a complete source-level checking judgment yet. It exposes the message or branch payload specification but does not itself establish that a sent/received value inhabits that type, substitute a communicated semantic value into a dependent continuation, perform grammar recognition, or prove offer exhaustiveness. Those responsibilities remain assigned to the later value/evidence, recognition, and process/control slices.

## Next checker slices

1. Process/control outcomes: `Continue`, `Return`, `Closed`, and `Failed`, including terminal-path linear-resource rules.
2. Grammar-backed receive with `PendingRecv`, scoped raw-byte loans, recognition, and commit.
3. Bidirectional value checking and explicit definitional/propositional equality boundary.
4. Refinements, evidence matching, explicit transport, and stable residual obligation generation.
5. Deterministic focusing/elaboration rules.
6. Parser and surface-to-Core elaboration.
7. Conformance harness over the accepted/rejected `.phil` corpus.
8. Assurance-ledger handoff and manifest verification.

## Explicit current non-goals

The checker still does not claim source-level Phil conformance. In particular it does not parse Phil syntax, project dependent session types from a global protocol, perform dependent value substitution, gate grammar-backed receives on complete recognition, solve refinements, validate the upload protocol end-to-end, or lower to systems/LLVM IR. Those claims remain premature until the corresponding checker competence exists.
