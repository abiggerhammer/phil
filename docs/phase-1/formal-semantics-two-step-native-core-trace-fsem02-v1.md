# FSEM-02: native Core two-step protocol trace and conditional model frame

**Status:** non-normative, bounded implementation-conformance evidence. Neither a full native source program nor a universal Haskell-to-Rocq simulation.

## Independently executable two-generation resource trace

The production Haskell Core test `test/Phase1FSEM02TwoStepCoreTraceMain.hs` instantiates a bounded two-message binary protocol using the actual `instantiateBinaryProtocol` and `projectProtocolRole` entry points with explicit externally supplied declaration/role/instance inputs. Both dual projections have two consecutive U8 Send/Receive heads followed by `End Done`. No semantic permission is inferred from occurrence names.

For both independently checked peers, `checkProtocolAction` advances initial predecessor to intermediate successor and then intermediate predecessor to terminal `End` successor. At each checkpoint the test observes **both** the real `protocolEndpoints` metadata map and `protocolResources.linearBindings`: exactly one successor is live, old predecessor absent, and exact role/instance/session preserved. Both terminal Closes then consume the final endpoints. The trace separately injects stale initial predecessors (exact `ProtocolEndpointUnknown`), wrong continuation action (`ProtocolSessionError (UnexpectedSessionAction ReceiveAction ...)`) and wrong externally supplied role (`ProtocolRoleMismatch`) between the two successful steps; each rejected probe leaves the previously committed contexts intact. All tests reject exact error constructors, not an arbitrary failure.

The dedicated workflow also executes existing whole-source, production Grammar-v1 accepted and minimally rejected Ping/Choice witnesses with their exact source rejection checks. **Those fixtures are independent single-transition programs**. The constructed two-step Core session is *not* claimed to have been admitted by a two-step Grammar-v1 source program; its protocol-family authority is a separate external test input.

## Proof relation (conditional, not a native refinement)

`proof/Phil/Core/FSEM02TwoStepNativeCoreFrame.v` composes the already checked two-step successor-chain consumption lemma with the independent two-peer loan/spectator frame theorem. Under explicit externally supplied source/rendezvous admissions, exact predecessor=successor chaining, and well-formed Ping/Choice heads, two successful modeled steps both consume the exact predecessor generations, preserve borrowed-loan collections, and retain disjoint spectators' original bindings.

This extensional Rocq `ResourceContext` fact does *not* establish that Haskell `Map` equality reflects the Rocq carrier for arbitrary states. It does not connect a native trace to a decoded Rocq observation or prove native diagnostic-class equivalence; the recorded Haskell checks are finite, independent conformance tests. `SessionStep.v` and `ConcurrencySemantics.v` are still referenced through existing conditional bridge modules. No `Admitted`, `Axiom` or `Parameter` is added.

## Missing stronger obligation

A complete **source-accepted two-step** protocol program with producer-fidelity evidence, versioned exact source/Core state observation, and independently proved or checked Rocq decoding/replay relation remains outstanding. Protocol instance, activation, partner matching, selected root, disposal, assurance authority, and the actual scheduler are not manufactured by this isolated test. FSEM-02 remains open; no normative graduation.
