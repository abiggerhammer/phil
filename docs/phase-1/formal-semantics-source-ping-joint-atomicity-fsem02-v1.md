# FSEM-02: source Ping joint successor freshness and atomic refusal

**Status:** bounded, non-normative source-conformance and conditional proof-model evidence for [issue #1613](https://github.com/abiggerhammer/phil/issues/1613). Follows protected merged #1742. No normative grammar, semantic authority, TCB or branch protection changes.

The complete accepted parsed Grammar-v1 witness [accepted.phil](../../test/fixtures/fsem02-protocol-progression-v1/accepted.phil) supplies both actual checked component Send/Receive predecessor and successor binder identities, and exact dual projected local heads from the independently instantiated Ping protocol family. The production **Phil.Core.ProcessRendezvous.checkProcessCommunication** is then exercised with **both** source-derived sides in one synchronous **JointProcessRendezvous**, not merely two successful local checkProtocolAction calls.

The active process population is independently supplied as an explicit test premise. This test does NOT derive activation, architecture binds, protocol authority or disposal permission from source syntax. Those have separate, bounded coverage in existing INT-008 and FSEM-02 source-to-activation tests.

**Production Haskell regression:** test/Phase1FSEM02ProtocolProgressionMain.hs performs these checks.

- The accepted joint Ping step consumes both exact source predecessor occurrences and produces both typed End Done successor bindings, with unchanged nominal protocol instance/roles and no extra process contexts.
- An occupied successor in either side's unrestricted, affine or linear resource map produces an exact **RendezvousProtocolError process (ProtocolSessionError (SessionResourceError (DuplicateBinding successor)))** with no successful paired state. In particular, a *peer-only* failure does not commit a valid sender's progress.
- An independently forged receiver metadata-only successor collision produces an exact **RendezvousProtocolError process (ProtocolEndpointMetadataConflict successor)**. This inconsistent context is a deliberate negative control, not admitted well-formed source.
- An unrelated borrowed affine server owner and its active loan survive a successful paired rendezvous. Replaying the original source pair fails with exact **RendezvousEndpointNotOwnedByProcess**, not a synthetic fresh endpoint.
- The complete minimally rejected [stale-close.phil](../../test/fixtures/fsem02-protocol-progression-v1/stale-close.phil) source remains checked against the exact **GrammarV1ComponentSendCloseCloseMismatch** constructor. The adversarial occupied resource maps are native-state tests using independently source-derived binder names, not additional whole-source programs.

**Rocq 9.2:** proof/Phil/Core/FSEM02PingJointAtomicity.v defines an explicit option-valued synchronous pair over FSEM02ProtocolHeadProgression.v and SessionStep.v. It proves that either local failure yields no joint successor; success implies both predecessor consumptions, exact model continuation types and affine/loan frames on each side. The local session heads, duality, exact nominal/process authority and native error classification remain premises outside the theorem. ConcurrencySemantics.v's rendezvous validity is **not** derived by this model, and no universal Haskell-to-Rocq refinement theorem is claimed. No new Admitted/Axiom/Parameter declarations.

**Still open:** general source semantics, scheduler/environment choices, unrestricted implementation-refinement and restricted payload ownership transfer across arbitrary programs, architecture/activation authority, terminal disposal, selected root, effects/assurance discharge and FSEM-02 exit criteria. No claimed global progress, fairness, deadlock freedom or full Phase 1 coverage.
