# FSEM-02 Terminal OBS-V1 — terminal close and stale retry source/Core wire

**Status: bounded, non-normative; FSEM-02 remains OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Actual source and protocol-state inputs

This slice reuses the exact complete Grammar-v1 accepted `Bytes[8]` Send/Receive/Close program in `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` and all three minimally rejected source Close-operand mutants from OBS-V1. The production `grammarV1CheckRestrictedSourceRendezvous` and `grammarV1CheckRestrictedSourceClose` execute under **independently supplied** protocol instance/revision, roles, activation/owner occurrence ledger, network, `Done` terminal outcome and spectator; none of these are inferred as authority from source syntax.

The native `restrictedTerminalObservationWire` first verifies the five OBS-V1 actual source/Core verdicts and exact source binder errors, then checks the real successor-state terminal close with the same parsed source. It distinguishes three **ordered finite scenarios** on that particular source and supplied state:

1. `NotDone` receiver outcome is rejected with exact `CloseOutcomeMismatch Done NotDone` and receiver process provenance, without a committed transition.
2. `Done` on both peers accepts terminal Close, retiring exactly the sender and receiver successor endpoint occurrence keys and preserving the transferred `Bytes[8]` owner and independent affine spectator.
3. Replaying the same source close on the **actual post-close state** rejects `EndpointClosureOccurrenceUnknown` for the original sender successor, without resurrecting a closed endpoint.

The existing `sourceCloseReplay` and `sourceCloseWrongOutcome` native regressions additionally establish source close determinism, exact endpoint/resource-map removal and refusal; the new emitter fails closed on an unexpected constructor or binder identity. The initial source parser and relevant Core transitions remain production Haskell, not modeled substitutions. This does not prove that arbitrary source inputs admit these premises.

## Independently compiled finite Rocq check

`test/Phase1FSEM02RestrictedSourceTransferMain.hs emit-rocq-terminal-observation` emits a deterministic three-verdict `proof/Phil/Core/FSEM02TerminalObservationData.v` **only after** all native replay assertions pass. CI byte-compares the generated file to the committed datum. Rocq 9.2 compiles the tag model, datum and five finite facts: exact event order, one committed terminal close, refusal positions, no second close in the suffix, and exactly one transfer in the preceding OBS-V1 datum. No Admitted/Axiom/Parameter is introduced.

These finite checks are **not** a universal Haskell-to-Rocq implementation-refinement theorem, not a complete `SessionStep.v`/`ConcurrencySemantics.v` simulation, and not an extracted evaluator or universal terminal-disposal law. Protocol instance/revision, message boundary, activation, selected root, external outcome and disposal authority remain explicit external premises. No normative syntax, TCB, privileged publication or branch rules are changed.

Preflight: `.github/workflows/fsem02-terminal-observation-preflight.yml`. A draft PR is allowed only after exact work-HEAD focused strict GHC 9.6.7 / Rocq 9.2 success; a protected merge additionally requires all exact PR-head checks and fresh post-ready claim guard, no untrusted skips, then matching audited claim release.
