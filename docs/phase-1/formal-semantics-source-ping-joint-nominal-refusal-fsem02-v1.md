# FSEM-02: source Ping two-process nominal refusal

**Status:** bounded non-normative Haskell/Core source-conformance and conditional Rocq evidence for issue #1613, following protected merged #1743. Normative syntax, TCB and external authority are unchanged.

The complete accepted source witness is [accepted Ping](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil), with checked component Send/Receive endpoint occurrence names and independently projected dual Ping heads. The minimal rejected witness is [stale-close Ping](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) with exact GrammarV1ComponentSendCloseCloseMismatch. Both are executed by the same Haskell regression suite. The two active processes, selected nominal protocol instance and role authority are **separate supplied premises**.

The production Phil.Core.ProcessRendezvous.checkProcessCommunication is called once with a *joint* SendReceiveRendezvous. Wrong request-side instances and forged stored endpoint instances on **either** peer reject with exact RendezvousProtocolInstanceMismatch process expected actual. Wrong requested or stored roles on **either** peer reject with exact RendezvousProtocolRoleMismatch process expected actual. A simultaneous instance-and-role mismatch gives the instance diagnostic first. Every refusal returns a Left rather than a one-sided updated process map, while the valid source-derived control consumes both exact predecessor occurrences, produces correctly typed End Done successors, preserves a borrowed affine spectator and loan, and rejects stale replay with RendezvousEndpointNotOwnedByProcess.

These malicious metadata contexts are deliberate native-state adversarial controls; they are **not** described as second accepted complete source programs. No source syntax manufactures protocol authority.

Rocq 9.2 proof/Phil/Core/FSEM02PingJointNominalRefusal.v gates the existing paired local progression model from FSEM02PingJointAtomicity.v with four explicit externally checked nominal flags. Each failed gate has a no-paired-successor theorem, and successful composition requires all four true plus the two local progression successes. No new Admitted/Axiom/Parameter. No generalized Haskell-to-Rocq refinement theorem is claimed.

**Still open:** scheduler and environment, full selected-root process activation semantics, restricted payload transfer for arbitrary programs, disposal authority, effects and assurance, universal implementation refinement, and FSEM-02 closure.
