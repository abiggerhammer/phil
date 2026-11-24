# FSEM-02 — symmetric borrowed spectator frame for paired Ping (bounded v1)

**NON-NORMATIVE; FSEM-02 remains OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Extends the [paired local/joint Ping bridge](formal-semantics-paired-local-joint-bridge-fsem02-v1.md), not accepted grammar or authority.

## Conditional rule and inputs

Given complete production-checked Grammar-v1 Ping source, dual projected Client Send/Server Receive heads, independently supplied protocol instance/revision, role/endpoint identities, an activated two-process network, and separate exact resource states, a successful pair of local steps consumes both old endpoint bindings and installs exact continuing successors. It also frames any distinct spectator and each process's current shared-loan set. Source acceptance and rendezvous admission are named independent inputs; neither creates root/activation/disposal authority or proves `ConcurrencySemantics.RendezvousValid`.

## Executable acceptance and exact refusals

`test/Phase1FSEM02ProtocolProgressionMain.hs` uses the accepted complete source `test/fixtures/fsem02-protocol-progression-v1/accepted.phil`, creates a separately owned Client affine `TyUInt 16` spectator and Server affine `TyUInt 8` spectator under independent active `startSharedLoan` calls, then checks full native `Map ProcessKey ProtocolContext` equality between separately executed production `checkProtocolAction` Send/Receive and production `checkProcessCommunication` joint Ping. Both affine bindings and both loan maps are checked unchanged, along with exact predecessor retirement, successor typing, nominal identity and unchanged-state replay.

The minimally rejected complete source `test/fixtures/fsem02-protocol-progression-v1/stale-close.phil` rejects as exact `GrammarV1ComponentSendCloseCloseMismatch`. Missing Client or Server predecessor metadata refuses with exact `RendezvousEndpointNotOwnedByProcess` (correct process and name), produces no paired successor, and leaves independently retried original-state success unchanged. Consumed joint predecessors cannot be replayed.

## Machine-checked model and limitations

In `proof/Phil/Core/FSEM02PairedLocalJointBridge.v`, `fsem02PairedReplayFramesBothLoansAndIndependentLinearSpectators` proves that any successful continuing paired local replay preserves *both* abstract `sharedLoans` functions and every linear binding except each local predecessor/successor pair. Its premises include independently admitted selected continuing heads. This is a conditional Rocq model theorem, with no new `Admitted`, `Axiom`, or `Parameter`.

The Haskell equality is finite checked conformance, **not** universal native Map/Set-to-Rocq function refinement. Abstract `endpointType` is not proved identical to native `TyEndpoint`. Activation, source ownership authorization, root, restricted payload transfer authority, fairness and global source-to-Core trace fidelity remain open. No normative graduation is claimed.

Focused work-branch CI: `.github/workflows/fsem02-ping-dual-loan-frame-preflight.yml`; merge requires all current exact-HEAD required checks and fresh post-ready claim guard.
