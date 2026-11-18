# FSEM-02: protocol binder versus restricted resource atomicity

**Non-normative bounded observation; FSEM-02 remains open.** This slice follows the projected-head/binder ordering of #1891 and tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).

## Explicit state and rule

The accepted whole-source restricted `Bytes[8]` Send/Receive fixture is parsed and checked by the production Grammar-v1 adapter. The external binary protocol instance, message boundary certificate, process activation/owner index, role/projected-head metadata, selected root and disposal authority are **supplied premises**, never inferred from spelling.

Given a source-valid Send/Receive pair, externally authorized sender owner and endpoint heads, the production `checkRestrictedProcessRendezvous` gate checks the *protocol-authorized receiver message binder before moving resources*. It then consumes the exact sender restricted linear payload and inserts the exact receiving linear resource. A false prerequisite yields a typed `Left` with **no successor**, rather than a partially committed endpoint or payload transfer.

The hostile state simultaneously (a) uses a forged external protocol-message receiver binder, (b) deletes the sender's actual linear payload while keeping the owner occurrence index, and (c) occupies the receiver's intended binding. The real Haskell checker must first reject with `RestrictedMessageReceiverBinderMismatch`; repair **only** the protocol binder to expose `RestrictedMessageSenderResourceError ... (UnknownBinding ...)`; repair **only** the sender resource to expose `RestrictedMessageReceiverResourceError ... (DuplicateBinding ...)`. Independently restoring the authorized original state permits the exact transfer with both endpoint successors and the borrowed affine spectator unchanged. Repeating a bad input must not silently mutate it.

A one-operand whole-source `close endpoint` in place of `close done` produces the exact source error `GrammarV1ComponentSendCloseCloseMismatch` before any external defect. This is a *source* negative, not an invented proof or authority error.

The [native executable regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) exercises the production parsed-source adapter; the [six separate conditional Rocq 9.2 laws](../../proof/Phil/Core/FSEM02BinderResourceAtomicity.v) model gate ordering, absence of a successor for refusals, exact boolean resource movement on success and unchanged spectator flags. Rocq booleans abstract native `Map`/`ResourceContext`/nominal endpoint identities and are not a mechanized Haskell simulation. Relation to [SessionStep](../../proof/Phil/Core/SessionStep.v) and [ConcurrencySemantics](../../proof/Phil/Core/ConcurrencySemantics.v) is bounded observation, not general refinement or new protocol, root, termination, or assurance authority.

The [unprivileged strict focused preflight](../../.github/workflows/fsem02-binder-resource-atomicity-preflight.yml) runs GHC 9.6.7 `-Werror`, this source executable, Rocq 9.2 proof compilation and a new-admissions scan before broad CI.
