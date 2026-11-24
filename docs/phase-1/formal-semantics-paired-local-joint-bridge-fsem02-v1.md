# FSEM-02 paired local progression / joint Ping bridge (bounded v1)

**NON-NORMATIVE; FSEM-02 remains OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This is a deliberately small evidence seam across existing `SessionStep.v`, `ConcurrencySemantics.v`, and production `Phil.Core.Protocol` / `ProcessRendezvous`. No Phase 1 syntax, accepted TCB, external authority or normative semantics changed.

## Explicit inputs and conditional judgment

For one previously accepted complete Grammar-v1 Ping source, the production source checker resolves exact Client/Server predecessor and successor endpoint names and the checked dual binary-family projections. **Separately** supplied protocol instance/revision, roles, activated process population and endpoint state authorize the Core actions. The offer/close source spelling never creates protocol, root or disposal authority.

The candidate *paired* local model is

```text
(sourceAccepted, rendezvousAdmitted, local sender state, local receiver state)
  -> (both exact local successors) | None
```

where `None` means *refused without a paired successor*, **not** a runtime mutation/rollback guarantee. Sender and receiver continuations each consume exactly their own predecessor, introduce an exact fresh continuation in their own local resource context, and preserve their own active loans. It is essential that `rendezvousAdmitted` is an **external boolean observation**; it does **not** prove `ConcurrencySemantics.RendezvousValid`.

The separate conditional payload theorem additionally **requires** `RendezvousValid`, the exact restricted subject and successful local steps. It then composes `SessionStep` predecessor consumption with `ConcurrencySemantics.restricted_rendezvous_transfers_exact_owner`. This theorem does not create a message-boundary certificate or assert that the Haskell checker establishes the premise.

## Independently checked positive and negative production witnesses

- **Accepted source:** `test/fixtures/fsem02-protocol-progression-v1/accepted.phil`, parsed and checked by the existing production Grammar-v1 Ping family, component, binder and projection checker. The new regression `sourcePingPairedLocalJointEquality` executes two real `checkProtocolAction` calls and the actual synchronous `checkProcessCommunication` on the **same** independently instantiated, activated process network. It requires exact complete `Map ProcessKey ProtocolContext` equality between the joint result and the separately checked sender/receiver successors, including a Server affine spectator and outstanding shared loan; mere matching endpoint counts are insufficient.
- **Minimally rejected complete source:** `test/fixtures/fsem02-protocol-progression-v1/stale-close.phil`. Its altered endpoint operand must still produce the exact `GrammarV1ComponentSendCloseCloseMismatch` class with the `done` versus `endpoint` binder identities, not arbitrary parse failure.
- **Native negative peers:** removing either original predecessor's protocol endpoint metadata produces exact `RendezvousEndpointNotOwnedByProcess` including process key and endpoint name. This pure checker returns `Left` with **no paired successor**; retrying unchanged original state must reproduce the exact accepted two-sided result. Replaying an already-consumed original joint request also refuses exactly.

The Haskell witness is **not** a proof that all runtime joint steps equal the paired Rocq model. It compares two independent production Haskell paths on an identified source witness, which is a narrower and useful seam than finite observation tags alone.

## Machine-checked Rocq boundary

`proof/Phil/Core/FSEM02PairedLocalJointBridge.v` defines a computable, success-only two-local-pair replay (with externally supplied admission flags), proves both missing-predecessor refusals and no-successor results for rejected source/admission, and proves that a successful pair has both exact predecessor removals, exact abstract continuation token insertions, and loan preservation. A final theorem composes conditional two-sided local progression with `ConcurrencySemantics.RendezvousValid` to obtain exact restricted owner movement. No new `Admitted`, `Axiom` or `Parameter` is introduced; the historical `SessionStep.endpointType` remains abstract.

**Open obligations:** actual native `TyEndpoint` equality to abstract Rocq `endpointType`; native Map/Set-to-model state relation; deriving proof-side `RendezvousValid` from checked native activation/message admission; universal source-to-Core trace fidelity; unrestricted/affine/linear full message contexts; architecture/root selection and terminal disposition; scheduler independence; normative graduation. No global source-to-Rocq refinement theorem is claimed.

Focused work-branch CI: `.github/workflows/fsem02-paired-local-joint-bridge-preflight.yml`. A draft PR still requires full exact-HEAD success, all required CI, fresh post-ready claim guard, clean protected expected-head squash, and independently audited exact claim release.
