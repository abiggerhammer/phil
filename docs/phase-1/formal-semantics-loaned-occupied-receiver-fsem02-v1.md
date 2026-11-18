# FSEM-02: loaned occupied receiver refuses restricted Linear transfer

**Non-normative, bounded production-source/Core conformance and conditional Rocq 9.2 gate model.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Extends the borrowed endpoint/sender progression (#1898/#1900) and cross-mode receiver collision test (#1897), without changing normative syntax, semantic authority, resource implementation, or TCB.

## Source judgment and exact native refusal order

The [production restricted source adapter](../../src/Phil/Surface/GrammarV1/ComponentRestrictedRendezvous.hs) parses the complete [accepted Grammar-v1 `Bytes[8]` Send/Receive source](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil) and independently replays the separately admitted Core protocol/owner state. The sender's actual linear payload is consumed *before* insertion of the receiver's exact source-resolved name into its Linear resource context. That insertion rejects any already bound name across Linear/Affine/Unrestricted maps, irrespective of an active shared loan of an existing Linear or Affine receiver binding. The transition is a pure `Either` value; rejection yields no partial successor.

The [native Haskell regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) independently creates an occupied receiver destination in each of **Linear** and **Affine** mode with actual `insertBinding`, then starts and ends a real `startSharedLoan`/`endSharedLoan` on that binding. A separate real shared loan holds the sender payload. Both are adversarial Core states, **not** newly validated activations.

For **both** modes, the exact failure/repair sequence is:

1. Sender payload still borrowed, receiver name occupied and also borrowed: `RestrictedMessageSenderResourceError ... (OwnerBorrowed senderPayload)` with exact sender process/owner identity.
2. End only sender's loan: `RestrictedMessageReceiverResourceError ... (DuplicateBinding receiverName)` with exact receiver process/name, even though the existing receiver owner remains borrowed.
3. End receiver's loan too: **the same** `DuplicateBinding` refusal, because ending a loan does not erase its binding.
4. Remove the independently inserted occupied receiver binding and restore the original source/activation-derived state: exact original-state equality and previously verified successful transfer with endpoint successors, moved payload occurrence and affine spectator preservation.

With *both* hostile faults present, changing just the sender's `close done;` to `close endpoint;` in the complete parsed source must still yield exactly `GrammarV1ComponentSendCloseCloseMismatch`, before Core resource errors.

## Conditional proof and limits

Nine [Rocq 9.2 finite-gate lemmas](../../proof/Phil/Core/FSEM02LoanedOccupiedReceiver.v) prove source/authority-before-resource rejection, sender-loan precedence, occupied-receiver rejection despite an active loan, preservation of the duplicate when the loan ends, a modeled authorized transfer with spectator frame, and absence of a dangling receiver loan *only given the explicit coherent-state premise*. These are not an extraction or simulation proof of Haskell's `Map`/`Set` loan representation or the source checker.

External concrete protocol instance and role authority, message-boundary contract, selected root, activated process and resource ledger, exact resolved owner/binder occurrence identities, disposal and assurance authority are **premises**, never inferred from source spelling. This slice provides no general Haskell-to-Rocq refinement, compiler correctness, normative rule adoption, fairness/liveness or FSEM-02 closure.

The [strict branch preflight workflow](../../.github/workflows/fsem02-loaned-occupied-receiver-preflight.yml) checks warning-free GHC 9.6.7 production library and actual accepted/rejected source execution, Rocq 9.2 compilation and no newly admitted statements **before any broad CI PR**.
