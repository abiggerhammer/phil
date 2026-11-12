# FSEM-02: source offer successor freshness and spectator frame

**Status: bounded non-normative source/native/conditional-model conformance; roadmap #1613 remains open.** This follows merged #1733 and does not promote any Phase 1 semantic authority.

## Judgments and externally supplied inputs

Given one complete, parsed Grammar-v1 server offer source, independently admitted binary Choice protocol instance/role, its original activated and exactly source-bound live Core endpoint, an externally chosen label (`Go` or `Cancel`), and a caller-provided successor occurrence name:

```text
Sigma; source; P; choice=Go;     successor=fresh |- offer => P_EndDone
Sigma; source; P; choice=Cancel; successor=fresh |- offer => P_EndCancel
successor=old                             => rejected(SuccessorReusesEndpointName old)
successor in Gamma OR A OR Delta          => rejected(DuplicateBinding successor)
old already consumed                      => rejected(ProtocolEndpointUnknown old)
unrelated borrowed affine owner remains    => exact same owner and active loan after offer and End close
```

The duplicate error is nested exactly under `GrammarV1OfferReplayProtocolError (ProtocolSessionError (SessionResourceError (DuplicateBinding ...)))`. The same-name error is nested under `ProtocolSessionError (SuccessorReusesEndpointName ...)`. The caller's supplied name must be distinct from *all* current resource owners; a new End occurrence cannot silently overwrite an unrestricted, affine, or linear spectator. A failing `Either` never returns a successful post-error context.

## Executable and machine-checked evidence

- Accepted complete source: `test/fixtures/fsem02-source-offer-v1/accepted.phil`; minimally rejected complete source: `test/fixtures/fsem02-branch-outcome-separation-v1/missing-cancel.phil`, which fails specifically `GrammarV1ComponentOfferMissingArm "Cancel"`.
- Expanded `test/Phase1FSEM02BranchOutcomeSeparationMain.hs` runs the real production Grammar-v1 parser, component coverage and `grammarV1ReplayComponentOffer`. Both choice labels are checked against three distinct occupied-successor modes, against predecessor/successor identity alias, and against an unrelated borrowed affine spectator. The successful alternative paths and separately authorized End closes preserve the full original spectator resources and active loan; exact live endpoint and linear resource maps are compared, not merely the accept/reject bit. Previous branch isolation and arm-order negative cases remain active.
- `proof/Phil/Core/FSEM02OfferSuccessorFreshness.v` composes the existing `Context`, `SessionStep` and FSEM-02 choice model. It proves occupied *unrelated* successors fail in the extensional resource model for any of three structural-mode bindings, both labels reject same-name successors, and under separate successful-step premises both choice alternatives preserve unrelated linear owner lookups and active loans. No new Axiom, Parameter or Admitted.
- Early strict focused runner: `.github/workflows/fsem02-offer-successor-freshness-preflight.yml`; the full PR CI and fresh post-ready claim guard remain independent gates.

## Trust boundary / nonclaims

Protocol admission and projection, source-to-Core endpoint binder identity, activation, selected label, fresh successor choice and separate End disposition/close permission are **external inputs**. The test does not execute general offer branch bodies or infer source authority. Rocq's `endpointType` is an existing abstract model token, not a proof that it is native `TyEndpoint`. The claim is not universal Haskell-to-Rocq refinement, arbitrary source execution, architecture/root or assurance certification, and does not close FSEM-02. No normative grammar, TCB or branch protection changes.
