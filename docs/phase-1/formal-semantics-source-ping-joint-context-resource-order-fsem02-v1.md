# FSEM-02 — source Ping joint context/resource diagnostic precedence (non-normative)

Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613). This is a bounded **nonterminal Send/Receive** check, not another terminal End/Close case. It changes no Phase 1 normative semantics.

## Checked production behavior

The independently accepted whole-source [Ping witness](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) and the minimally rejected [stale-close witness](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) are replayed through the production Grammar-v1 checker with an exact rejection constructor. Accepted source supplies Client/Server Send/Receive predecessor and successor identities with checked dual session heads. The actual Core `checkProcessCommunication` is separately supplied an **external** two-process network, nominal protocol instance, role assignments and process-local protocol/resource contexts. Source syntax does not grant these external authorities.

The new `sourcePingJointMissingContextPrecedence` test in [Phase1FSEM02ProtocolProgressionMain.hs](../../test/Phase1FSEM02ProtocolProgressionMain.hs) supplies three deliberate faults: both process-local contexts absent; Client context absent while Server has an incorrect `TyUInt 8` linear predecessor; and Server context absent with the equivalent bad Client resource. The production joint checker must reject with the **exact** `RendezvousMissingProtocolContext` process (Client first if both are absent), never speculate about peer resources or produce a one-sided successor.

Restoring the absent context exposes the remaining precise `RendezvousProtocolError process (ProtocolEndpointResourceTypeMismatch endpoint (TyUInt 8))`. Restoring *both* independently checked contexts admits a paired transition, with exact source-derived predecessor consumption and End-typed successor identity and metadata on both sides, preserved unrelated borrowed affine spectator and loan, deterministic replay from the original state, and stale-predecessor refusal after consumption. Malformed contexts and resources are deliberate external test inputs, not permissions for source programs or implicit rollback.

## Conditional Rocq model and trust boundary

[Proof file FSEM02PingJointContextGates.v](../../proof/Phil/Core/FSEM02PingJointContextGates.v) adds seven bounded Rocq 9.2 theorems. Explicit presence booleans reject absent process contexts before the previously proved resource agreement gates; restoring both contexts exposes those gates. Conditional successful paired admission requires both contexts and both resource gates, with exact predecessor consumption, successor type and affine/loan framing inherited from [FSEM02PingJointAtomicity.v](../../proof/Phil/Core/FSEM02PingJointAtomicity.v).

The boolean observations are **premises**, not an established Haskell Map-to-Rocq correspondence, an authority derivation, a proof about scheduler fairness, complete architecture/root/activation/disposal validity, a universal source-to-implementation refinement or a new concrete `TyEndpoint` representation of abstract `endpointType`. No new `Admitted`, `Axiom` or `Parameter` is introduced.

Focused GHC 9.6.7 and Rocq 9.2 preflight is [fsem02-ping-joint-context-resource-preflight.yml](../../.github/workflows/fsem02-ping-joint-context-resource-preflight.yml). Full exact-head PR CI, fresh post-ready FSEM claim guard and protected expected-head merge remain separate mandatory gates. FSEM-02 stays **OPEN and non-normative**.
