# FSEM-02 — paired local Choice versus joint rendezvous (bounded v1)

**Status:** non-normative, pending exact-head focused and full CI; tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This does not modify the accepted Phase 1 grammar, TCB or semantic authority.

## Proposed judgment and inputs

Given separately source-checked, dual-projected Client `Select(label)` and Server `Offer(label)` heads, an **externally chosen** matching peer label, an independently supplied nominal binary instance, activated process network and exact native resource contexts, the proposed pair either consumes both predecessor endpoints and installs their distinct selected successors, or returns the exact production rejection with no partial successor.

This slice tests the finite Go and Cancel cases with the actual production `checkProtocolAction` local Select and Offer checks, then compares the **entire two-process native context map** to the independently executed `grammarV1CheckJointSourceChoice` / Core rendezvous result. A separate affine spectator is put under an active shared loan; the test checks both its affine binding and loan set remain equal. Reusing either consumed local predecessor, replaying the spent joint predecessor, or supplying a wrong external peer label must reject with the exact checked error class and identity. Pure rejected calls may not change valid replay from the original contexts.

**Accepted executable witnesses:** `test/fixtures/fsem02-source-choice-v1/accepted.phil` for Go, `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil` for Cancel, and separately parsed `test/fixtures/fsem02-source-offer-v1/accepted.phil`. **Minimally rejected executable witness:** `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil`, checked by the same production test suite with exact `GrammarV1ComponentOfferArmBodyUnsupported` rejection; `test/fixtures/fsem02-source-choice-v1/unknown-label.phil` is an additional exact unlisted-arm negative. Neither source fixture conveys process activation authority by itself.

## Independent Rocq conditions and boundaries

`proof/Phil/Core/FSEM02PairedChoiceJointBridge.v` gates the existing `FSEM02JointSourceChoice.v` model by independently supplied source-acceptance and rendezvous-admission Boolean premises. Its finite-model theorems refuse missing admission, unaccepted source, peer mismatch and absent source arms, and show exact pair predecessor consumption and selected successor typing after successful replay. A separate conditional theorem composes the abstract local result with `ConcurrencySemantics.RendezvousValid` **only if that proposition is independently supplied**, preserving the restricted payload owner-transfer premise rather than fabricating one.

The actual source-to-Core equality check is a bounded Haskell test, **not** a universally proved model refinement. Abstract `SessionStep.endpointType` has not been justified as native `TyEndpoint`; native `Map`/`Set` representation, protocol-family and role identity, message admission, selected root, activation/disposal, physical scheduling and full message/loan transfer remain distinct proof obligations. No `Admitted`, `Axiom` or `Parameter` is added. No language-wide type safety, liveness or normative graduation is claimed.

The pre-PR focused workflow `.github/workflows/fsem02-paired-choice-joint-bridge-preflight.yml` requires strict GHC 9.6.7 (actual accepted/rejected Grammar-v1 and Core witness checks) plus Rocq 9.2 compilation. A PR additionally requires the exclusive prebranch claim, exact-head full checks, fresh post-ready FSEM claim guard, and ordinary protected squash/claim release.
