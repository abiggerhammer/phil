# FSEM-02 Ping joint nominal/projection/resource gate priority (non-normative)

**Status:** bounded Haskell source-conformance regression and independent conditional Rocq 9.2 model, **not** adopted semantics, full implementation refinement, or global soundness. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Exact witnessed source and external premises

The accepted parsed Grammar-v1 Ping source is test/fixtures/fsem02-protocol-progression-v1/accepted.phil; the minimally rejected source is stale-close.phil in the same folder. The production source checker identifies exact Client Send / Server Receive predecessor and successor names and expected dual heads. The negative source rejects with the exact existing stale-close binder error, not with an opaque parser failure.

The test separately supplies an already-instantiated **active** two-process Core network, external binary protocol instance/revision and role grants, original endpoint contexts and resources. None of those nominal or lifecycle authorities is inferred from the source spelling. The independent borrowed affine spectator is held by Server throughout.

The joint evaluator is the actual production Phil.Core.ProcessRendezvous.checkProcessCommunication, not a mock. Its operation order is:

1. Validate both active process identities and both process-local contexts (the earlier missing-context slice covers this).
2. Validate Client nominal instance and projected Send head, then Server nominal instance and projected Receive head.
3. Only then run the Client and Server ProtocolAction resource gates, consume both predecessors and install exact End-typed successors atomically.

## Negative and positive witnesses

For **each** endpoint, the test injects a foreign requested instance, a wrong stored terminal End head and a wrong non-endpoint linear TyUInt 8 binding simultaneously. The exact native error is first RendezvousProtocolInstanceMismatch. Correcting the request but not the stored head exposes RendezvousProjectionSessionMismatch (the expected source head versus End). Correcting the head but not the resource exposes RendezvousProtocolError / ProtocolEndpointResourceTypeMismatch. This checks independent repairs rather than accepting any rejection.

A cross-peer compound case gives Client a bad predecessor linear resource while Server has both a bad resource and a foreign request instance. **Server nominal refusal precedes Client resource refusal** because both projection/nominal validations finish before either resource transition. Restoring Server's request then exposes Client's resource fault. Restoring only Client's resource exposes Server's remaining fault. Restoring both original contexts permits exactly one successful joint step, retires both original names, installs both End-typed successors with the proper instance/role, preserves Server's affine loan and rejects a stale repeat. All malformed attempts have no successor and never mutate the original state.

The separate [Rocq classifier](../../proof/Phil/Core/FSEM02PingJointGatePriority.v) is a finite boolean-premise model with distinct Client and Server nominal, head, and resource failure classes. Its short-circuit theorems expose the same prescribed ordering. Its gated optional step reduces to the previously checked [FSEM02PingJointAtomicity](../../proof/Phil/Core/FSEM02PingJointAtomicity.v) resource transition only after external nominal and projection premises. This is *not* an independently extracted implementation or proof that all Haskell diagnostics agree with the classifier.

## Exact verification and boundaries

The dedicated [focused Haskell/Rocq gate](../../.github/workflows/fsem02-ping-joint-gate-priority-preflight.yml) runs strict warning-free GHC 9.6.7 with the accepted and rejected source fixtures and Rocq 9.2 with no new Axiom, Parameter or Admitted. Green HEAD/workflow evidence must be recorded separately; file presence is not proof that it ran.

Related models: proof/Phil/Core/SessionStep.v and ConcurrencySemantics.v (independent transition/protocol abstractions), FSEM02PingJointAtomicity.v (bounded two-sided predecessor consumption, successor installation, framing), and the earlier FSEM02PingJointContextGates.v (external process-context admission). No new syntax, TCB, branch protection, network authority, runtime scheduler policy, disposal permission or global Haskell-to-Rocq theorem. FSEM-02 stays open.
