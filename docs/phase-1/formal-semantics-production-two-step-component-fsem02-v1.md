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

## Follow-on FSEM-02 second-payload lexical scope gate (non-normative)

The second Send payload is now resolved in the real lexical scope **after** the first `let`, never in the original component parameter scope. In the accepted complete `DoublePing`, `second` still resolves to its U8 component parameter. The minimally rejected complete-source fixture `second-local-payload.phil` changes only `send second on middle` to `send middle on middle`: `middle` is **in scope** but is the first endpoint successor (a let-pattern binder), not a permitted component-parameter payload in this narrow checker. It must produce the distinct production diagnostic `ChainSecondPayloadNotParameter`, rather than the incorrect `ChainUnresolvedOccurrence` obtained when consulting pre-let scope. Existing stale-second-predecessor and wrong-Close controls are unchanged.

The source premise is lexical binder kind, **not** complete type/protocol checking: the checker still does not validate arbitrary Send payload types, legitimate endpoint delegation, full component elaboration, process authority or source-to-Core refinement. Active name shadowing is already rejected independently by `GrammarV1BindLocal`; it is not used as an accepted fixture or mischaracterized as newly discovered compiler acceptance. The conditional Rocq name inequality only expresses what follows from supplied distinct identities; production binder fidelity remains a separate Haskell test and nonclaim.

## Follow-on DoublePing two-Receive U8 annotation envelope (non-normative)

For the **externally established** `DoublePing` server projection
(`Receive U8; Receive U8; End Done`), the bounded production checker
now verifies that each written Receive annotation is exactly the original
source form `U8`. The accepted complete source stays accepted. Minimally
rejected original-source `receive-first-u16.phil` and
`receive-second-u16.phil` modify one annotation each and must obtain the
specific production `ChainFirstReceiveAnnotationNotU8` or
`ChainSecondReceiveAnnotationNotU8` result. These are **restricted
U8 witness-envelope refusals**, not universal type errors: a different
protocol could legitimately receive `U16`.

The caller separately establishes the protocol instance, projected expected
heads and duality, then supplies its independently justified declaration
identity to the bounded checker. The checker does **not** derive that nominal
authority from source names, nor infer expected types for arbitrary protocol
instances, validate arbitrary received payload expressions, perform general
component compilation, or certify architecture, activation, rendezvous,
disposal or assurance. The Rocq theorem
`fsem02TwoReceiveU8WitnessGateSound` establishes only that a finite
two-annotation **model** gate can succeed when both modeled tags are U8.
There is no proof of compiler AST-to-model fidelity or Haskell-to-Rocq
refinement. Native predecessor/successor/Close replay remains separately
tested. This is non-normative and FSEM-02 remains open.
