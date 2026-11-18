# FSEM-02 — exact restricted receiver-binder correspondence gate

**Status:** bounded and non-normative; tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). This slice addresses a distinct *source-to-authorized-protocol correspondence premise*, rather than extending four-site fault-mask counts. No Phase 1 grammar, native authority rule, TCB, or production runtime is changed.

## Judgment and authority boundary

For a source-checked restricted `Bytes[8]` Send/Receive pair, let `b_s` be the **declaration-rooted resolved receive-pattern payload binder** and `b_p` the binder already carried by the **independently admitted** protocol message occurrence. The proposed conditional owner transition is:

```text
SourceAccepted(s) ∧ MessageAdmitted(p) ∧ HeadsValid(Σ)
∧ b_s = b_p ∧ AuthorizedOccurrence/OwnerLedger(Σ)
  ⊢ (s, p, Σ) --restricted send/receive--> Σ'
otherwise: rejected (precise original source/Core error), no successor
```

The equality is of semantic binder identities, not display names. An exact string match is **necessary, never sufficient**: it does not infer protocol instance, message boundary contract, role, process activation, restricted ownership, root, disposal authority, or assurance.

## Real executable source/native witnesses

The existing accepted whole-source [restricted Send/Receive fixture](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil) has an authorized generic protocol instance with a boundary-message contract and binder explicitly chosen to match the checker-resolved receive binder. The minimally [rejected stale-close source](../../test/fixtures/fsem02-restricted-source-transfer-v1/rejected-stale-close.phil) must still reject as exact `GrammarV1ComponentSendCloseCloseMismatch`.

The strict executable [Haskell regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) now also changes **only the source receive-pattern display binder** from `received` to `delivery`, reparses/rechecks the accepted source, verifies the declaration-rooted semantic identity has not shifted, and requires the actual production restricted rendezvous to succeed with the independently matching protocol binder. Using the display-level `value` as the supposedly authorized message binder still must fail with exact `RestrictedMessageReceiverBinderMismatch`; no binder remapping is attempted. Original accepted, stale-close, protocol-binder mismatch, owner and head negative cases remain active.

## Conditional Rocq result and nonclaims

[The Rocq 9.2 model](../../proof/Phil/Core/FSEM02RestrictedReceiverBinderGate.v) explicitly guards the existing `fsem02RestrictedSourceTransfer` conditional transition on exact source/protocol binder equality. It proves (i) wrong binder cannot yield any owner successor even when other admission facts hold, (ii) success implies matching binder, source/message/head admission, exact single-occurrence restricted payload transfer, successor-owner identities and preservation of all unrelated owners, and (iii) matching names alone never admit rejected source. The proof reuses the existing conditional owner-map transition rather than assuming production Haskell simulation.

**Not proved:** universal source alpha-equivalence, parser or Haskell-`Map` to Rocq refinement, nominal instance/boundary authority inference, automatically checked message admissibility, all-construct source interpreter, actual scheduler, global progress/termination, FSEM-02 completion or normative graduation. The source display-rename check is one finite native witness; the theorem is over the *already supplied* semantic binder identities.

The [focused work-branch preflight](../../.github/workflows/fsem02-restricted-receiver-binder-gate-preflight.yml) requires strict GHC 9.6.7 `-Wall -Werror`, real source/native accepted and exact negative cases, and Rocq 9.2 admission-free proof compilation before a broad CI draft PR. Exact-head claim guard, all required PR checks, protected expected-HEAD merge and verified claim release remain separate gates.
