# FSEM-02 Close-order OBS-V1 — source/Core two-order terminal confluence

**Status: bounded, NON-NORMATIVE; FSEM-02 remains OPEN.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Witness, judgment and authority

The strict native regression uses the unchanged accepted complete Grammar-v1 `Bytes[8]` send/receive/close source and the three single/both stale-Close minimally rejected source variants from `test/fixtures/fsem02-restricted-source-transfer-v1/`. It first requires the existing OBS-V1 and Terminal OBS-V1 exact error-class checks; it does not replace source validation with a handwritten model.

Independent *external* inputs to the finite checker include the protocol instance, message boundary certificate, roles, activated process-network and occurrence owner ledger, terminal `Done` outcomes, spectator and resource/disposal authority. The source code itself does **not** create this authorization, certify an architecture root or discharge assurance obligations.

The observed restricted joint transition is:
- checked `Send/Receive` consumes two predecessor endpoint occurrences and transfers one exact `Bytes[8]` linear payload owner;
- sender-first and receiver-first `End Done` Close orders independently consume the two distinct successor endpoint occurrences;
- both final complete Core `ProcessCommunicationState` values are exactly equal; the receiver-first intermediate state has retired only the receiver endpoint and preserved the sender endpoint, transferred payload and affine spectator;
- attempting to close **either** successor on **either** final state yields exact native `EndpointClosureOccurrenceUnknown` with the process and endpoint identities, never a recreated owner.

These checks exercise production `grammarV1CheckRestrictedSourceCloseDiamond` and `closeProcessEndpointState`, not a mock transition; native `Either Left` refusals have no exposed successor.

## Checked finite producer wire and separately compiled model

`test/Phase1FSEM02RestrictedSourceTransferMain.hs emit-rocq-close-order-observation` emits six ordered tags: sender-first/receiver-first convergence then four exact retired-endpoint refusals. The strict GHC 9.6.7 preflight byte-compares the generated Rocq datum to `FSEM02CloseOrderObservationData.v`; Rocq 9.2 independently compiles the datum, five finite event facts, and three conditional model laws for distinct-operand close commutation, payload/spectator framing, and terminal no-replay. The model uses two boolean endpoint-occurrence bits and two preserved owner-presence bits; these are *not* a general interpretation of production Haskell maps.

No `Admitted`, `Axiom` or `Parameter` is introduced. The tests do **not** prove universal Haskell→Rocq refinement, source elaboration fidelity, general `SessionStep.v`/`ConcurrencySemantics.v` simulation, terminal disposal correctness, scheduler independence for arbitrary networks, or normative authority. A finite checked observation is evidence for this source and explicit environment, not a semantic theorem about all programs.

Preflight: `.github/workflows/fsem02-close-order-observation-preflight.yml`. Broad exact-head required checks, fresh post-ready claim guard, normal protected expected-HEAD squash merge and audited matching claim release remain mandatory.
