# Phil proof corpus

This directory contains the checked mechanized evidence for Phil assurance obligations.

The human-facing logic ledger lives in Drive. The repository is authoritative for whether an obligation is actually discharged at a particular commit.

## Conventions

- Rocq is the canonical prover for normative Phil metatheory and refinement proofs.
- Every theorem intended to discharge a ledger obligation names the stable obligation ID in a nearby comment.
- `Admitted`, undeclared axioms, and opaque trust shortcuts do **not** discharge an obligation. If one is temporarily necessary, the corresponding assumption must remain explicit in the ledger.
- Small proof models may abstract implementation details that are irrelevant to the theorem, but those abstractions must be stated explicitly and tightened before stronger claims depend on them.
- Proofs should follow the implementation slices closely enough that semantic drift is visible in review.

## Discharged slices

### PHIL-SESSION-DUAL-001 — session duality

`proof/Phil/Core/Session.v` establishes that session duality is involutive. Message types are opaque in this slice because `dualSession` preserves them unchanged; the theorem is about the session protocol structure implemented by `src/Phil/Core/Session.hs`.

### PHIL-CTX-LIN-001 — exact linear consumption

`proof/Phil/Core/Context.v` models binding maps and the active-loan set extensionally as lookup functions. On every successful `consumeLinear`, it proves that:

- the consumed owner was bound to the returned type before the step;
- the requested linear owner is absent afterward;
- every other linear lookup is unchanged; and
- unrestricted bindings, affine bindings, and the loan set are unchanged.

The success theorem deliberately abstracts the implementation's error-classification details (`WrongStructuralMode` versus unknown binding), because those branches cannot occur under the theorem's successful-result premise. Finite-map representation details remain outside this slice.

### PHIL-PROC-SEQ-001 — process sequencing

`proof/Phil/Core/Process.v` mirrors the `Either`-style failure behavior of `sequenceFlow` while treating `CheckState` as opaque. It proves that `Continue` is exactly the control case delegated to the continuation and that every non-`Continue` path (`Return`, `Closed`, or `Failed`) occurs unchanged in every successful sequencing result.

The proof uses a structurally recursive presentation equivalent to the implementation's `mapM` plus concatenation; list order and multiplicity are preserved.

## Session label selection

`PHIL-SESSION-LABEL-001` models the current `ensureUniqueLabels` / `selectBranch` boundary. The Haskell implementation uses `Data.Set`; the proof checks uniqueness structurally over the proof-oriented branch spine. The mechanized claims are that duplicate-label branch sets are rejected before lookup, absent requested labels are rejected, every successful lookup occurs only in a globally unique branch set where the requested label occurs exactly once, and the successful payload/continuation is exactly the result of the requested-label lookup. Payload types and continuations are carried through unchanged and are not inspected by this theorem.
