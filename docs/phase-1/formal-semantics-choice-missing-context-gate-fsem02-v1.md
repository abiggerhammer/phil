# FSEM-02 — terminal End missing protocol-context gate (non-normative)

**Boundary.** Source-checked Go/Done and Cancel/Cancel Select/Offer witnesses are
`test/fixtures/fsem02-source-choice-v1/accepted.phil`,
`test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil`, and the
separately parsed Server offer
`test/fixtures/fsem02-source-offer-v1/accepted.phil`. The minimally rejected,
complete source `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil`
must still reject with exact `GrammarV1ComponentOfferArmBodyUnsupported`.
The extra owner-map/context mutations below are **adversarial Core probes**,
not operations granted by that source.

## Explicit ordered gates and failure states

For a requested active process `p`, selected terminal End `n`, externally
supplied protocol instance/role/outcome and state `S`, production
`closeProcessEndpointState` checks, in order:

1. process membership (`EndpointClosureUnknownProcess`);
2. active activation (`EndpointClosureProcessNotActive`);
3. presence of a protocol context (`EndpointClosureMissingProtocolContext`);
4. **exact** owner cardinality of pairs `(p,n)`:
   zero = `EndpointClosureOccurrenceUnknown`, two or more =
   `EndpointClosureOccurrenceAmbiguous` with all keys;
5. only for a unique owner, the separately authorized nominal/session End
   checker, with exact `EndpointClosureProtocolError` on mismatch;
6. only after an allowed step, atomically retire that endpoint owner and
   update its checked protocol context.

Every error returns *no successor*; it cannot confer nominal authority or
silently repair a missing context. Context presence is not a substitute for
protocol-instance, role or outcome authorization.

## Executed source/native bridge

`test/Phase1FSEM02SourceJointChoiceMain.hs` independently checks the accepted
and rejected source cases above and builds the actual source-derived joint
successor `ProcessCommunicationState`. It removes only the requested
Client protocol context under three finite owner populations (0, 1, 2 exact
matches), supplying intentionally invalid nominal claims. All six probes,
including peer-first End closure, must report precisely
`EndpointClosureMissingProtocolContext` before owner and nominal errors.
The independent peer remains closable, the altered Client owner map is
preserved and the borrowed affine spectator is unchanged.

The test then **restores the exact previously checked context as an external
test operation**, not a compiler inference: zero owners now reject
`EndpointClosureOccurrenceUnknown`, two reject complete
`EndpointClosureOccurrenceAmbiguous`, while one reaches the exact nominal
instance-mismatch gate. The correctly authorized unique case recovers the
two End closure orders with full native state equality.

## Conditional Rocq model

`proof/Phil/Core/FSEM02ChoiceMissingContextGate.v` defines an explicitly
ordered, finite, non-normative gate outcome model distinguishing the missing
context, zero/multiple ownership, nominal refusal and successful retirement.
It proves missing-context precedence/no successor, post-restoration exact
owner branches, and that a unique owner alone never grants nominal authority.
Its booleans are **supplied external observations**, not proofs of actual
process population, activation, context, or protocol grants. A complete native
Haskell Map-to-Rocq correspondence and universal refinement remain open.
It does not modify `SessionStep.v`, `ConcurrencySemantics.v`, syntax, TCB,
scheduling, architecture-root or assurance authority. FSEM-02 remains open.
