# FSEM-02: source-derived two-step binder-chain replay (bounded v1)

**Status:** non-normative, narrow source-structure/lexical-identity conformance test and conditional Rocq corollaries. Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613).

The accepted complete Grammar-v1 fixture `test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil` declares a two-message binary `DoublePing` session with Client Send/Send/End and Server Receive/Receive/End, paired components, an architecture, explicit role/process bindings and a selected program. The dedicated executable `test/Phase1FSEM02TwoStepSourceBinderChainMain.hs` parses the **whole source** with the production structural parser, derives the protocol family through production duality checking and generic instantiation under explicitly supplied declaration/interface identity, and uses the production lexical-scope and pattern-binder machinery to resolve two successive successor endpoint identities **by declaration-rooted binder key** rather than textual spelling. It then runs two actual `checkProtocolAction` transitions per peer, testing exact before/intermediate/final resource-map and endpoint checkpoints and two terminal Closes. The consumed original predecessor must reject as exactly `ProtocolEndpointUnknown` after the first successful transition, not as a generic parse failure.

Two minimally different, structurally parsed complete-source negatives assert the checker-local exact diagnostics `ChainSecondPredecessorMismatch` (the second Send reuses the initial source endpoint instead of its first successor) and `ChainTerminalCloseMismatch` (Close names the first successor rather than the second). These are explicit results of the **bounded test-side binder-chain checker**, not evidence that the general Phil component compiler already produces these diagnostic constructors. Separate production single-step Ping controls are rerun, with existing independently checked source rejection.

The proposed source judgement is partial:

```text
Γ; source-component ⊢ endpoint₀ --Send/Receive--> endpoint₁
                    --Send/Receive--> endpoint₂ --Close--> End
```

Its premises require complete Grammar-v1 structural parsing, valid closed dual protocol templates, exact resolved endpoint binder-key chaining, externally supplied protocol lineage/role metadata, and an admissible two-message concrete U8 projection. A mismatched second predecessor or terminal Close is rejected *before* native replay. The test does not silently interpret a missing source constructor or unclassified binder as an opaque success.

The Rocq 9.2 module `proof/Phil/Core/FSEM02TwoStepSourceBinderChain.v` reuses checked abstract two-step theorems: conditional successful paired replay consumes both predecessor generations exactly; using the original sender predecessor again for a second Ping step refuses while retaining the first committed pair. It adds no `Admitted`, `Axiom`, or `Parameter`. The Haskell binder-key observations are **not** encoded as Rocq input evidence, and the Rocq premises are not automatically discharged by source parsing.

**Nonclaims and obligations:** This is not production generalized component-body elaboration, typechecking of every payload expression, a source-to-Core trace producer-fidelity theorem, a single network-level rendezvous executor, an extracted reference interpreter, or universal native Haskell Map/Set-to-Rocq refinement. The test's source-checking component is deliberately narrower than the full Phase 1 compiler. External protocol instance, selected root, process activation, owner mapping, rendezvous/scheduler decisions, disposal, effect and assurance authority remain independent. Neither syntax nor TCB nor normative semantics is changed. FSEM-02 is still incomplete.

**Exact checks:** dedicated focused GitHub workflow `.github/workflows/fsem02-two-step-source-binder-preflight.yml` runs strict GHC 9.6.7 (`-Wall -Werror`) and Rocq 9.2.0 on the same source SHA, plus existing source controls; full PR checks and post-ready FSEM claim guard are separate required gates.
