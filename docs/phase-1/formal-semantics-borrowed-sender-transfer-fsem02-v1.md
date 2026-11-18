# FSEM-02: outstanding shared loan blocks restricted sender payload transfer

**Status: non-normative bounded production Haskell conformance and separately modeled conditional Rocq 9.2 laws.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613); extends the receiver collision tests in #1897 without granting new authority or changing normative syntax.

## Rule, contexts and admitted premises

The real [Core ResourceContext](../../src/Phil/Core/Context.hs) records unrestricted, affine and linear bindings and a `sharedLoans` set. `consumeLinear owner` returns exactly `OwnerBorrowed owner` if the shared loan is active, *before* it consumes the linear binding. The production [restricted source adapter](../../src/Phil/Surface/GrammarV1/ComponentRestrictedRendezvous.hs) replays an accepted, complete parsed Grammar-v1 `Bytes[8]` Send/Receive fixture into the Core atomic rendezvous. In that transition, sender payload consumption precedes receiver insertion and both endpoint owner updates: on any `Left`, the pure state has **no successor**.

The actual source checker/activation is grounded in the accepted [complete source fixture](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil). Independent protocol instance and roles, generic concrete-message boundary contract, activated process population, exact owner occurrence and declaration-rooted payload identities, projected session heads, selected-root and disposal/assurance authority remain **external premises**. The source text neither confers a borrow nor proves any such authority.

## Two independent faults and ordered repairs

The [production executable regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) creates a hostile Core sender state by invoking the **actual `startSharedLoan`** on the existing linear `Bytes[8]` payload owner, keeping the original binding and exact owner name. Separately, it occupies the receiver's authorized linear destination using actual `insertBinding`. Both hostile maps deliberately differ from the previously validated activation; they are test inputs, **not** evidence that the activation authorizes a borrowed transfer.

* Both faults: exact `RestrictedMessageSenderResourceError (OwnerBorrowed ownerName)` wins over the receiver collision, with exact sender process and owner identity; no partial successor and deterministic refusal.
* Restore only the receiver: the sender loan still blocks transfer with the identical `OwnerBorrowed` classification.
* End the sender loan only: exact `RestrictedMessageReceiverResourceError (DuplicateBinding receiverName)` is exposed, with the source-derived receiver name and process.
* Restore both independently: existing authorized `acceptedReplay` checks exact source transfer, predecessor consumption, endpoint successor identity, payload occurrence owner migration and independent affine spectator.
* A **minimally rejected complete source** changes only `close done;` to `close endpoint;`. Its exact `GrammarV1ComponentSendCloseCloseMismatch` must precede either external resource error.

The separate [nine conditional Rocq lemmas](../../proof/Phil/Core/FSEM02BorrowedSenderTransfer.v) model the order of source, external/binder, sender-presence, loan, type and receiver-occupancy gates; no-successor on refusals; and accepted modeled sender consumption and spectator framing after all repairs. The finite flags are explicit premises, **not** proof that native Haskell Map/Set state refines this Rocq record. Connection to [SessionStep.v](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) is bounded tested transition correspondence, not a general source-to-Core or Haskell-to-Rocq simulation.

[Focused unprivileged preflight](../../.github/workflows/fsem02-borrowed-sender-transfer-preflight.yml) checks warning-free GHC 9.6.7, exact accepted/rejected production source replay, Rocq 9.2 compilation and no new `Admitted`, `Axiom` or `Parameter` before opening a draft PR. Broad exact-HEAD required checks, fresh post-ready claim guard and normal protected expected-HEAD squash merge remain mandatory.

**Open:** FSEM-02 closure; universal Haskell/Rocq resource representation refinement, full-source operational/extracted interpreter coverage, independent protocol/root/disposal/assurance qualification, and any normative graduation.
