# FSEM-02: same-type sender in wrong structural mode refuses restricted transfer

**Non-normative source/Core conformance and conditional Rocq 9.2 decision model.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This extends the typed-but-wrong-*type* sender regression (#1895) to a different failure: the payload has the right `Bytes[8]` type and exact source-resolved name, but exists only in an **Affine or Unrestricted** Haskell resource map instead of the required Linear map.

## Bounded judgment and tested refusal ladder

The complete [accepted Grammar-v1 Send/Receive witness](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil) is parsed and checked by the [production restricted adapter](../../src/Phil/Surface/GrammarV1/ComponentRestrictedRendezvous.hs). Independently admitted concrete protocol/owner/activation evidence requires a Linear `Bytes[8]` source payload. The [real native Haskell regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) removes that payload's existing Linear binding and uses actual `insertBinding` to install the same name and exact `Bytes[8]` type in either Affine or Unrestricted. Separately it fills the receiver's source-resolved destination in Linear, Affine or Unrestricted mode (six independent combinations). These states deliberately corrupt a resource snapshot; they are not fresh valid activations.

For each combination, exact diagnostic, state and repair observations are required:

1. Both faults: `RestrictedMessageSenderResourceError sender (WrongStructuralMode payload Linear actualMode)`, not a receiver insertion error. The exact sender process/name and actual `Affine`/`Unrestricted` mode are asserted.
2. Repair only the receiver: the identical structural-mode sender error persists, even though its type is exactly `Bytes[8]`.
3. Repair only the sender to its original Linear map: `RestrictedMessageReceiverResourceError receiver (DuplicateBinding destination)` reveals the independent cross-map receiver collision.
4. Repair both: the original full context is reconstructed exactly, and the existing accepted source replay checks consumed endpoint predecessors, exact successor identities, transferred payload ownership, and the affine spectator frame.

A *single changed Close operand* in the otherwise complete source (`close done;` → `close endpoint;`) must reject with `GrammarV1ComponentSendCloseCloseMismatch` ahead of all intentionally hostile Core resources. The production transition is a pure `Either`; every refusal yields no partially usable successor.

## Conditional proof boundary

Nine [Rocq 9.2 finite-gate lemmas](../../proof/Phil/Core/FSEM02CrossModeSenderPayload.v) prove source and external-authority precedence, wrong-mode before receiver collision, independent repair behavior, no modeled successor on refusal and framed modeled transfer on success. The model's structural-mode flags are **not** a proof of universal Haskell `Map`/`Set` correctness, actual source-to-Core simulation or `SessionStep.v`/`ConcurrencySemantics.v` refinement. The correspondence is via exact production witnesses and a separately proved bounded model.

Concrete protocol instance/role/message authority, activation/owner and resolved-binder occurrence identities, selected root, disposal and assurance evidence remain **independently supplied premises**; neither spelling nor modeled gates grant them. No normative syntax change, newly admitted language construct, TCB change, global type soundness, extracted interpreter, implementation refinement, liveness/fairness or FSEM-02 closure is claimed.

[Strict work-branch preflight](../../.github/workflows/fsem02-cross-mode-sender-preflight.yml) compiles warning-free production GHC 9.6.7 and executable accepted/rejected source tests, plus Rocq 9.2 proofs and the no-new-admissions scan, **before** broad PR CI.
