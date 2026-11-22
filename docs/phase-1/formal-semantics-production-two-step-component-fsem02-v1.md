# FSEM-02: bounded production two-step component checker (non-normative)

Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613). This slice follows merged #1976. It adds a **real production-library checker entry point**, not a general compiler acceptance promise.

`src/Phil/Surface/GrammarV1/ComponentTwoStepChain.hs` contains `checkSendChain` and `checkReceiveChain`. They take an explicitly supplied `DeclarationKey` and a structurally parsed `GrammarV1ComponentDecl`. They accept only the exact three-statement double-Send or double-Receive plus terminal-Close shapes. Using the real parameter-scope, local-occurrence, and pattern-binder implementations, the checker resolves the first endpoint and two successors by *binder identity*, not display text. Each second step must use the preceding successor; terminal Close must consume the final successor. No source spelling manufactures a nominal protocol instance, root, activation, owner or assurance permission.

For the narrow fragment, an accepted Client chain has the shape
`let middle = send first on endpoint; let done = send second on middle; close done;`.
An accepted Server chain has two tuple-Receive statements followed by `close done`. The partial judgment is:

```text
Γ; declaration-key; component ⊢ endpoint₀ ─action₁→ endpoint₁
                                       ─action₂→ endpoint₂ ─Close→ End
```

The boundary checks that `endpoint₀` is a component parameter and, for Send, that both payload occurrences resolve to component parameters. It uses actual pattern-binding scope transitions to identify `endpoint₁` and `endpoint₂`. The explicitly classified outcomes include `ChainSecondPredecessorMismatch`, `ChainTerminalCloseMismatch`, `ChainUnresolvedOccurrence`, `ChainPatternShape`, and `ChainUnsupportedSourceShape`. A wrong source shape returns a rejection, not a silent opaque success.

The existing complete-source `DoublePing` accepted fixture and its *minimally modified* second-stale and wrong-Close fixtures now pass through these **production-library** constructors from `test/Phase1FSEM02TwoStepSourceBinderChainMain.hs`, replacing the checker that previously existed only inside the test. The test separately checks production protocol family/duality projection, actual native `Core.Protocol` two-transition replay, precise stale `ProtocolEndpointUnknown`, resource-map progression, and exact Close consumption. Its native request and process authority remain explicit external inputs.

`proof/Phil/Core/FSEM02TwoStepSourceBinderChain.v` retains the conditional two-generation predecessor-consumption and stale-prefix theorems and adds two exact binder-freshness implications, requiring the explicit assumption `original <> successor`. Rocq 9.2 checks these statements. They are not proofs that the Haskell binder resolver refines Rocq, and no proof premise is retroactively discharged by source parsing.

**Limits:** This is bounded production library competence for one concrete two-step shape, **not** generalized component-body checking or acceptance of the entire component through the compiler's ordinary entry point. It does not check every payload expression type, architectural realization, process activation, scheduler/rendezvous decision, disposal or obligation discharge. A valid source in another shape can be rejected as unsupported. No general source-to-Core producer fidelity, Haskell-to-Rocq simulation, or normative rule graduation is claimed.

Focused exact-work-head CI: `.github/workflows/fsem02-production-two-step-component-preflight.yml` strictly builds the Haskell library and runs this checker plus previous native/source controls under GHC 9.6.7 `-Wall -Werror`, independently compiling the Rocq dependency closure. PR-wide required checks and fresh post-ready claim guard remain separate merge gates.
