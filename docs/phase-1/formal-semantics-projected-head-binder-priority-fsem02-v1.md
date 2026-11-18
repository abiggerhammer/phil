# FSEM-02: projected session-head diagnostics before external protocol binder

**Status: bounded, non-normative; FSEM-02 remains incomplete.** Tracks issue #1613 and composes, without replacing, the earlier source/dual-identity priority slice in #1889.

## Exact decision boundaries

The independently checked restricted complete source must pass its Close-operand and written receiver-type gates before entering the native restricted Send/Receive Core checker. That checker verifies the activation-owned sender occurrence first, then validates the **live sender and receiver projected endpoint metadata against their linear resource sessions**, sender before receiver. Only after both independent protocol steps does it compare the message binder authorized by the external protocol against the resolved source receiver binder.

For the *tested* source and explicit external inputs, the diagnostic sequence for simultaneously corrupted owner, both projected heads and protocol binder is:

1. Wrong sender activation owner -> exact `RestrictedMessageOwnerMismatch`.
2. Repair only owner -> sender `RendezvousProtocolError (ProtocolEndpointSessionMismatch ...)`.
3. Repair sender projected session only -> receiver's corresponding exact session mismatch.
4. Repair receiver projected session -> exact `RestrictedMessageReceiverBinderMismatch` from the separately forged authorized message binder.
5. Independently restore valid protocol authority -> accepted native restricted transfer, exact endpoint successors, moved linear payload owner and preserved affine spectator.

A minimally modified source with `close endpoint` replacing `close done` is independently rejected as `GrammarV1ComponentSendCloseCloseMismatch` before *any* external fault. This does not imply that source syntax grants the external instance, selected root, activation, terminal disposal, message contract or scheduler.

The [production Haskell executable witness](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) exercises the complete reparsed source and actual `checkRestrictedProcessRendezvous` path; refusal cases must return `Left`, never an invented successor. The [eight conditional Rocq 9.2 theorems](../../proof/Phil/Core/FSEM02ProjectedHeadBinderPriority.v) prove the order of these independently supplied decision booleans and identity equalities, and that the modeled Ready result requires all gates. These are **finite implementation-conformance tests plus a separate proof-side decision model**, not a universal Haskell-to-Rocq simulation, global error precedence theorem, normative semantics, or proof of transferable authority.

[Strict focused GHC/Rocq preflight](../../.github/workflows/fsem02-projected-head-binder-priority-preflight.yml) checks a warning-free native executable and admission-free proof compilation on the exact branch head before a draft PR.
