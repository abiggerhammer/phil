# FSEM-02: two-branch offer-arm order and exact replay (bounded v1)

**Non-normative source conformance, not FSEM-02 completion.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This slice fills a narrower gap left by the already merged source choice/End-prefix bridges: whether a *source offer arm listing order*, as distinct from the independently checked role's semantic label catalogue, can change the selected Core successor.

## Judgment, inputs and failure

With separately parsed and checked complete source programs `S` and `S'`, the *same externally admitted* binary protocol family/revision, projected Server role and original live endpoint/resource state `P`, and supplied label `l`/fresh successor `e'`:

```text
Σ ; P ; source-offer(S, labels=[Go,Cancel]) | l
  -> Core.Offer(l,e') -> P'
Σ ; P ; source-offer(S',labels=[Cancel,Go]) | l
  -> Core.Offer(l,e') -> P'
```

Both source arms must have distinct labels and cover the externally checked role's complete branch catalogue; their bodies must match the explicitly supported `return unit` fragment. The selected branch's `End` outcome, exact old/successor occurrence identity, protocol instance and Server role, complete `ProtocolContext` and following externally authorized local close must match. Arm order is not an endpoint-identity grant or a scheduler choice.

An otherwise complete source with a duplicated `Go` arm must reject **exactly** `GrammarV1ComponentOfferDuplicateArm "Go"`; it may not silently choose the first/last body. An old endpoint replay against the already consumed state must reject `GrammarV1OfferReplayProtocolError (ProtocolEndpointUnknown old)`. A live non-`Offer` head rejects `GrammarV1OfferReplayWrongLiveHead` with exact expected/actual session.

## Executable evidence

`test/Phase1FSEM02ChoiceArmOrderMain.hs` uses the production parser, binary protocol family/projection checker, source offer coverage checker, `grammarV1ReplayComponentOffer` and actual `checkProtocolAction`. The new complete `test/fixtures/fsem02-offer-arm-order-v1/reordered.phil` swaps only the two source offer-arm statements from the existing complete accepted source fixture. The existing complete `test/fixtures/fsem02-source-offer-v1/duplicate-arm.phil` supplies the minimal rejected duplicate.

For Go/Done **and** Cancel/Cancel, the differential test starts both replays from the same original full Core state and compares exact predecessor, successor and complete process protocol/resource context, verifies predecessor absence, typed successor, and the full result after the separately supplied local End close. It also checks the stale and wrong-head negative paths. No cached successor or silent opaque fallback supplies equality.

## Rocq model and trust boundary

`proof/Phil/Core/FSEM02OfferArmOrder.v` proves a **conditional two-branch** `offeredContinuation` and local offer-replay permutation theorem for distinct protocol branch labels, a duplicate-label/order-sensitivity counterproperty when continuations differ, and stale-endpoint non-success. The proof is parametric in the abstract `SessionStep` resource token; it does not identify that token with production `TyEndpoint`. These are model facts, **not** universal parser/projection/Haskell-to-Rocq refinement.

Inputs and remaining premises: checked source grammar/binders, external protocol admission and revision, role projection, original activation and occurrence ownership, external label and fresh successor, valid terminal End authorization. This slice **does not** independently admit a combined architecture, infer Server disposal from `return unit`, prove arbitrary branch permutations or an implementation scheduler, establish full FSEM-02 or FSEM-05 execution, discharge selected-root/assurance obligations, or promote normative semantics. Duplicate labels must be rejected by the production source coverage checker; the Rocq theorem intentionally requires distinct semantic branch labels.

Strict two-job GHC 9.6.7 `-Werror` / Rocq 9.2 focused preflight: `.github/workflows/fsem02-offer-arm-order-preflight.yml`. Full PR exact-head checks, fresh post-ready claim guard, protected merge and trusted exact-claim release remain independent gates.
