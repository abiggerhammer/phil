# FSEM-02 disjoint Ping pair schedule commutation (non-normative)

**Status:** bounded production Haskell source-conformance and independently conditional Rocq 9.2 finite-map correspondence, not normative Phase 1 semantics or a global refinement theorem. Tracks [issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## Admitted source versus external authority

The accepted [Grammar-v1 Ping fixture](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) is checked by the real source/Surface parser and establishes one Client Send and Server Receive plan with exact predecessor/successor binders and dual session heads. The minimally rejected [stale-close fixture](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) is independently checked to fail with its exact binder mismatch, not a parser-opaque fallback. The finite test *instantiates that checked plan twice* in four independently active process sites. Four-site architecture/root activation, binary instance/revision, role grants and initial local contexts are **external premises**; the source fixture does **not** authorize four actual source components or any scheduler policy.

## Production transitions and negative cases

The executable test runs the actual `Phil.Core.ProcessRendezvous.checkProcessCommunication` with disjoint requests A and B. A then B and B then A must yield exactly equal complete maps, including exact endpoint predecessor retirement, End-typed successor identity and process population. Executing only A leaves B's complete contexts unchanged and vice versa. Both predecessor requests must reject stale replay after the two steps, with exact first-Client process and binder diagnostics.

In the independent negative trial, B's Server projection is malformed to End. B rejects with the exact `RendezvousProjectionSessionMismatch` before A; A still advances, preserving the malformed B input. B continues to reject after A. Only explicitly restoring the B context permits its step, and the two-step result equals the healthy A/B schedule result. A failure returns no successful successor; a rejected `Either` is not an actual state transition.

## Bounded model and unproved premises

[The independent Rocq model](../../proof/Phil/Core/FSEM02PingDisjointPairs.v) lifts the previously checked two-process optional resource map writer from [FSEM02PingThreeProcessFrame](../../proof/Phil/Core/FSEM02PingThreeProcessFrame.v) to two disjoint pairs. With all four represented process keys assumed distinct and each successful pair's resource transition externally admitted, it proves commutation of the two writes, commutation of two successful optional steps, absence of a two-step successor after either refusal, and preservation of every fifth/uninvolved key. The source and Haskell tests exercise actual production endpoints; the Rocq theorem is about a finite `nat -> option ResourceContext` surrogate and does not prove native ProcessKey/Map correspondence, success of real endpoint validation, fairness, concurrent atomicity beyond sequential calls, general source-to-Rocq refinement, or `satisfies C`.

Related non-normative models: [SessionStep](../../proof/Phil/Core/SessionStep.v), [ConcurrencySemantics](../../proof/Phil/Core/ConcurrencySemantics.v), and [Ping joint atomicity](../../proof/Phil/Core/FSEM02PingJointAtomicity.v). No grammar, TCB, runtime, branch rule or accepted semantic authority is changed. FSEM-02 remains open.

The [focused GHC 9.6.7/Rocq 9.2 preflight](../../.github/workflows/fsem02-disjoint-ping-pair-preflight.yml) must pass on the exact branch HEAD before opening the draft PR; later full PR-head gates and post-ready claim guard are separately mandatory.
