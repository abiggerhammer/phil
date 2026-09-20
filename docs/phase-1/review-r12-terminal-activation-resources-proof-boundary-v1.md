# PHIL-P1-REVIEW-R12 proof boundary

This slice certifies Astra Review R12: constructing the Certified terminal runtime must preserve every process's exact activation resource context.

The terminal initializer is not permitted to reconstruct, weaken, erase, or invent process resources. It may attach protocol metadata and open-obligation state, but the resource projection of each supplied protocol context must be exactly the `ResourceContext` already produced by certified activation.

The boundary has two explicit stages.

First, `validateActivationPredecessor` requires:

- the supplied process-key set exactly matches `activationProcessContexts`;
- every activation process has a supplied protocol context;
- there are no unexpected supplied process contexts; and
- for every process, `protocolResources context == expectedResources`.

Second, `initializeProcessRuntimeWithObligations` stores the supplied protocol-context map directly as `runtimeProtocolContexts = contexts`. The Certified wrapper additionally requires the runtime invariant and exact network identity before returning `CertifiedTerminalRuntime`.

The normalized theorem therefore establishes the composition:

`activation resources == supplied protocol resources == initialized runtime resources`.

It also proves the corresponding fail-closed cases: a missing process context, an unexpected process context, or a replacement resource context cannot satisfy the initialization boundary. In particular, an empty replacement context cannot erase a live linear activation resource.

The permanent R12 controls live in `app/ConcurrencyTerminalProductionBindingMain.hs`: one test initializes from a real activation containing a live linear resource and checks exact preservation; another substitutes an empty protocol resource context and requires `ConcurrencyTerminalActivationResourceMismatch` with the exact process, expected resource context, and replacement resource context.

This slice composes with the existing `PHIL-CONC-ACTIVATE-001` and `PHIL-CONC-TERM-001` authorities. It does not redefine activation partitioning or terminal closure.

Concrete `Map` key-set traversal, `ResourceContext` structural equality, protocol metadata representation, obligation-map initialization, diagnostic ordering, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
