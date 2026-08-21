# Phil proof corpus

This directory contains the checked mechanized evidence for Phil assurance obligations.

The human-facing logic ledger lives in Drive. The repository is authoritative for whether an obligation is actually discharged at a particular commit.

## Conventions

- Rocq is the canonical prover for normative Phil metatheory and refinement proofs.
- Every theorem intended to discharge a ledger obligation names the stable obligation ID in a nearby comment.
- `Admitted`, undeclared axioms, and opaque trust shortcuts do **not** discharge an obligation. If one is temporarily necessary, the corresponding assumption must remain explicit in the ledger.
- Small proof models may abstract implementation details that are irrelevant to the theorem, but those abstractions must be stated explicitly and tightened before stronger claims depend on them.
- Proofs should follow the implementation slices closely enough that semantic drift is visible in review.

## First slice

`PHIL-SESSION-DUAL-001` establishes that session duality is involutive. The first model treats message types as opaque because `dualSession` preserves them unchanged; the theorem is therefore about the session protocol structure implemented by `src/Phil/Core/Session.hs`.
