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

### PHIL-SESSION-LABEL-001 — session label selection

`proof/Phil/Core/SessionLabel.v` models the current `ensureUniqueLabels` / `selectBranch` boundary. The Haskell implementation uses `Data.Set`; the proof checks uniqueness structurally over the proof-oriented branch spine. The mechanized claims are that duplicate-label branch sets are rejected before lookup, absent requested labels are rejected, every successful lookup occurs only in a globally unique branch set where the requested label occurs exactly once, and the successful payload/continuation is exactly the result of the requested-label lookup. Payload types and continuations are carried through unchanged and are not inspected by this theorem.

## Current proof slices

### PHIL-CTX-BIND-001 — exact fresh binding insertion

`proof/Phil/Core/Context.v` now also models `insertBinding`. A successful insertion proves that the inserted name was absent from all three structural binding maps, appears afterward in exactly the selected mode, leaves every unrelated lookup unchanged, and preserves the active-loan set. The proof uses the same extensional binding-map abstraction as `PHIL-CTX-LIN-001`; finite-map representation details and the concrete `DuplicateBinding` diagnostic payload remain outside the successful-result claim.

### PHIL-SESSION-STEP-001 — session progression resource discipline

`proof/Phil/Core/SessionStep.v` composes the binding-insertion and linear-consumption results around the common resource effects of `Phil.Core.Session`. For non-close progression it models the successful `consumeEndpoint`/`continueWith` path: the old linear endpoint is consumed, endpoint-name reuse is rejected, a fresh linear successor carrying the continuation is installed, unrelated linear lookups are unchanged, and active loans are preserved. For close it proves the old endpoint is consumed, no successor is installed, unrelated linear lookups are unchanged, and active loans are preserved.

This theorem deliberately isolates resource effects from session-head/action matching. The concrete Haskell `TyEndpoint` constructor is represented by an opaque proof-side `endpointType : Session -> Ty`; the theorem does not inspect endpoint payload types. Grammar-gated recognition and action correctness remain separate obligations rather than assumptions smuggled into the resource proof.
