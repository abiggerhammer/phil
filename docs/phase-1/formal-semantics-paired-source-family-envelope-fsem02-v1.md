# FSEM-02 — paired Ping/Choice source-family replay envelope (bounded v1)

**Non-normative; FSEM-02 remains open.** This is an explicit *integration* of the separately verified [paired Ping](formal-semantics-paired-ping-dual-loan-frame-fsem02-v1.md) and [paired Choice](formal-semantics-choice-dual-spectator-frame-fsem02-v1.md) fragments, not another native transition rule or additional source syntax. Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Proposed typed source-family observation

The partial judgment has independently supplied family `F ∈ {Ping, Choice}`, checked source/continuation evidence, paired old/successor endpoint identities, two complete resource contexts, and external source-admission and rendezvous-admission flags:

```text
(F, sourceAccepted, rendezvousAdmitted; heads, choice labels, peer;
 old1, next1, old2, next2; C1, C2) ==> Some(C1', C2') | None
```

`FSEM02PairedSourceFamilyEnvelope.v` dispatches to the existing `fsem02PairedLocalReplay` for Ping or `fsem02PairedChoiceReplay` for Choice. It proves (a) either missing admission forbids every successor, (b) success implies **both** admissions, (c) under separately supplied typed continuing-head/branch-continuation premises every successful family preserves both entire abstract loan functions and every unrelated linear lookup, (d) Ping missing either predecessor refuses, and (e) Choice wrong peer label refuses. The model does not downgrade failure into a successful fallback.

## Real runnable source evidence

Strict GHC 9.6.7 `-Wall -Werror` reruns both production suites, **not** a mocked interpreter:

- `test/Phase1FSEM02ProtocolProgressionMain.hs` checks the complete accepted `test/fixtures/fsem02-protocol-progression-v1/accepted.phil` Ping against real `checkProtocolAction` and `checkProcessCommunication`, including both active-loan spectators, typed successors, exact predecessor consumption, joint/local full-context equality, and deterministic replay. Its minimally changed `stale-close.phil` must reject as `GrammarV1ComponentSendCloseCloseMismatch`; stale actual Core endpoints must reject as `RendezvousEndpointNotOwnedByProcess`.
- `test/Phase1FSEM02SourceJointChoiceMain.hs` executes independently parsed accepted Go and Cancel witnesses against actual local Select/Offer and joint Choice checks, with separate borrowed affine spectators; its minimally rejected `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` and unlisted source choice retain the exact source/projection rejection required by the production suite. No silently opaque case becomes accepted.

The dedicated branch preflight compiles these production sources, executes the existing accepted/rejected suites, compiles both imported proof bridges plus the new module in Rocq 9.2, and rejects new `Admitted`, `Axiom` or `Parameter` in this module.

## Trust premises and limits

The two branches are *separate source programs* with separately checked protocol families, role/projection and endpoint metadata, external activated networks, source admission and rendezvous validity. This tagged model does **not** demonstrate one combined Ping-then-Choice source program, session choice across different protocol instances, actual network authorization, source-to-Rocq producer fidelity, native Haskell Map/Set-to-Rocq refinement, equality of `SessionStep.endpointType` and production `TyEndpoint`, or semantic error-class identity. In particular, its `None` observation forgets native diagnostic classes; the latter remain asserted by the separate strict executable Haskell suites. It is **not** the FSEM-05 complete Phase 1 interpreter or a proof of universal compiler refinement, fairness, progress or disposal authority.
