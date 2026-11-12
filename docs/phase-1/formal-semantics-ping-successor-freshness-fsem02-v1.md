# FSEM-02: source Ping successor freshness and borrowed-owner frame

**Status:** bounded, non-normative protocol-progression evidence. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Follows the protected Ping terminal nominal Close slice #1741. No normative syntax or semantic authority is changed.

The accepted complete Grammar-v1 Ping program `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` is parsed, checked and projected through the production source-to-Core adapters. The resulting **source-derived** Client Send and Server Receive predecessor and successor occurrence names and projected `Send U8 End Done` / `Receive U8 End Done` heads are replayed against the real `Phil.Core.Protocol.checkProtocolAction`. The actual protocol instance and roles remain **separately admitted external inputs**.

For **each** source-derived Send and Receive, `test/Phase1FSEM02ProtocolProgressionMain.hs` now tests:

- Occupied successor in any structural resource map (unrestricted Γ, affine A, linear Δ): precise `ProtocolSessionError (SessionResourceError (DuplicateBinding successor))` without a successful successor.
- A distinct metadata-only successor collision with no corresponding structural owner: precise `ProtocolEndpointMetadataConflict successor`. This explicitly adversarial inconsistent context is a negative control, *not* an admitted well-formed starting configuration.
- Reusing the predecessor itself as successor: precise `ProtocolSessionError (SuccessorReusesEndpointName predecessor)`.
- Positive continuation in the presence of an unrelated borrowed affine owner: exact predecessor consumption, correctly typed `End Done` successor, preservation of the full affine map, unrestricted map and active loan set. The next terminal Close consumes the successor without changing that spectator; attempting to reuse the original predecessor returns exact `ProtocolEndpointUnknown`.

The same harness retains the minimally rejected **whole-source** `test/fixtures/fsem02-protocol-progression-v1/stale-close.phil` with exact `GrammarV1ComponentSendCloseCloseMismatch`. Collision states are *adversarial native contexts built from source-derived binders*, not claims that a second complete source specimen elaborates into those states.

`proof/Phil/Core/FSEM02PingSuccessorFreshness.v` reuses `SessionStep.v`, `FSEM02ProtocolHeadProgression.v` and the earlier conditional occupied-successor lemma from `FSEM02OfferSuccessorFreshness.v`. It establishes fail-closed occupied/same-name continuation for both Ping actions and extensional affine-map/loan-set preservation on successful continuation in the **Rocq model**. Haskell source and proof-side lookup carriers have no universal refinement theorem here.

**Premises / nonclaims:** exact source→Core binders and role projections, nominal instance admission, architecture activation, message payload and scheduling/rendezvous, disposal authority, selected root, effects and assurance all remain outside the theorem. Neither a globally valid protocol scheduler, full admitted Phase 1 operational semantics, proof of the production Haskell implementation, nor FSEM-02 completion follows from these finite checks. `ConcurrencySemantics.v` still represents a separate conditional synchronous rendezvous model. No new `Admitted`, `Axiom`, or `Parameter` is introduced.
