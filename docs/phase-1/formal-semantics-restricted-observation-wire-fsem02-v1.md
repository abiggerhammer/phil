# FSEM-02 OBS-V1 — checked restricted source/Core observation wire

**Status: bounded and non-normative; FSEM-02 is OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Exact source judgments and proof input

The same complete Grammar-v1 accepted source used by
`test/Phase1FSEM02RestrictedSourceTransferMain.hs` authorizes no protocol
instance by itself: nominal protocol instance, roles, activation state,
message boundary, terminal outcomes, selected root and assurance evidence
are **separate test inputs**. The accepted source and the three minimal
Close-operand mutants are:
- `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil`
- `rejected-stale-close.phil` — sender consumes a predecessor again
- `rejected-receiver-stale-close.phil` — receiver consumes a predecessor again
- `rejected-both-stale-close.phil` — both predecessor Close errors

The test's `restrictedObservationWire` observes the actual production
`grammarV1CheckRestrictedSourceRendezvous` after checking source byte
relationships, exact source error constructors *and binder identities*,
the accepted owner's Linear `Bytes[8]` transfer, the two consumed original
endpoints, both fresh typed successor endpoints and preservation of an
independently activated affine spectator. It observes a fifth negative:
replaying the previously accepted source against its actual post-transfer
state must reject at the exact `RestrictedMessageOwnerMismatch` with the
receiver's transferred payload owner. Source refusals have no emitted
successor, because the production checker returns `Left`.

The OBS-V1 alphabet deliberately exposes only **five ordered verdicts**:
accepted transfer, stale sender, stale receiver, both stale (sender-first),
and post-transfer stale replay. This does not claim to serialize the
underlying complete production `Map`/`Set`, network state, scheduler or
all actual error fields. It is not a general trace codec.

## Checked producer-to-Rocq boundary

`test/Phase1FSEM02RestrictedSourceTransferMain.hs emit-rocq-observation`
produces the deterministic Rocq datum
`proof/Phil/Core/FSEM02RestrictedSourceObservationData.v` only after all
native replay/error checks pass. CI **byte-compares** its output to that
checked-in artifact, compiles
`FSEM02RestrictedSourceObservationModel.v`, the data and
`FSEM02RestrictedSourceObservationChecks.v` in Rocq 9.2, and scans for
new admissions. Four finite theorems establish the precise observed
verdict sequence, refusal-only suffix, and exactly one committed transfer
in this finite specimen.

The independently checked Rocq data is **not** an independently justified
producer-fidelity theorem, parser/execution simulation, complete
`SessionStep.v` or `ConcurrencySemantics.v` refinement, extracted
interpreter or arbitrary-source soundness result. Existing conditional
model premises are unchanged; malformed/unclassified outcomes fail closed
in Haskell rather than becoming a success/default event.

Preflight: `.github/workflows/fsem02-restricted-observation-preflight.yml`.
Before merging require strict GHC 9.6.7, Rocq 9.2, exact-current-head
CI and claim guard, fresh post-ready guard, protected expected-head squash
and matching audited claim release. No new TCB, normative grammar or
privileged CI behavior is introduced.
