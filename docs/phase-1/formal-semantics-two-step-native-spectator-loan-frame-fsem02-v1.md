# FSEM-02: native two-step spectator / borrowed-loan frame

**Status:** bounded, non-normative implementation conformance plus conditional Rocq proof. This does not admit a combined two-step Grammar-v1 source program.

## New production Core evidence

`test/Phase1FSEM02TwoStepSpectatorLoanFrameMain.hs` independently instantiates the real two-message binary protocol, obtains exact dual U8 projections, and checks real `Phil.Core.Protocol.checkProtocolAction` on each peer for two successive Send/Receive transitions and terminal Close. An additional *independently supplied* protocol endpoint (with distinct instance revision/role) and a separate affine `U8` owner under an active shared loan are present on each peer at every checkpoint.

For initial, first-success, first-refusal, second-success and post-Close checkpoints the test examines **all four** actual Haskell `ResourceContext` collections (`unrestrictedBindings`, `affineBindings`, `linearBindings`, `sharedLoans`) and the exact protocol metadata map. Both generations' consumed predecessors disappear; each continuation retains exact instance/role/session. The disjoint spectator endpoint and its linear resource stay byte-for-byte equal by Haskell value equality across both steps, and the separately borrowed affine owner and active loan stay present. Exact `ProtocolEndpointUnknown`, `UnexpectedSessionAction ReceiveAction` and `ProtocolRoleMismatch` negative probes sit *between* admitted transitions and do not supply a successor context. After terminal Close, the unrelated spectator and loan remain live; `endSharedLoan` explicitly removes only the loan state, not the owner or spectator.

The dedicated strict GHC 9.6.7 preflight also executes existing production accepted and minimally rejected **separate** source Ping/Choice controls. These source checks do not derive the independently instantiated two-message Core protocol's authority.

## Bounded proof, independent from native execution

`proof/Phil/Core/FSEM02TwoStepNativeSpectatorLoanFrame.v` proves that a modeled first admitted paired Ping/Choice transition followed by a refused second transition yields the exact committed pair *and* retains two shared-loan collections and disjoint named linear spectators from the pre-first context. The proof is conditional on the first successful replay, its continuing-head hypotheses, exact spectator inequalities and second-step refusal. The existing `FSEM02TwoStepNativeCoreFrame.v` handles the successful second-step frame. Rocq 9.2 checks the new theorem with no `Admitted`, `Axiom` or `Parameter`.

**Nonclaims:** No source-accepted combined two-step trace, Haskell `Map`/`Set`-to-Rocq carrier refinement, general error-class simulation, scheduler/rendezvous proof or global FSEM-02 completion. Instance, activation, role binding, selected root, provenance, disposal and assurance authorities remain named external premises. A future versioned exact-checkpoint artifact and independently checked Rocq replay would be a stronger implementation bridge. `SessionStep.v` and `ConcurrencySemantics.v` are referenced through existing conditional proofs, not promoted to normative Phase 1 semantics.
