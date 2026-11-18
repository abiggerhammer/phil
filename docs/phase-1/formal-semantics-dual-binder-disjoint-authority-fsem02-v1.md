# FSEM-02: joint sender/receiver semantic-identity separation

**Status: bounded, non-normative; FSEM-02 incomplete.** See [#1613](https://github.com/abiggerhammer/phil/issues/1613).
This is a composition obligation beyond the independent
[sender/activation](formal-semantics-sender-activation-identity-gate-fsem02-v1.md)
and [receiver/protocol](formal-semantics-restricted-receiver-binder-gate-fsem02-v1.md)
checks, not another fault-mask enumeration.

Two binders in distinct component declarations may share the **same display
spelling** without sharing *semantic* identity. Let b_s and b_r be checked
declaration-rooted source identities; a_s and p_r independently supplied
activation owner and authorized protocol-message binder identities.
For independently admitted source, message and two live session heads, the
non-normative transition requires BOTH b_s = a_s and b_r = p_r before the
already modeled restricted Send/Receive transfer may yield successor ledger L'.
If either identity equality fails, there is no successor. Display spelling
does not supply a type, message certificate, owner grant, or instance.

**Accepted executable source witness:** Reparse the
[whole accepted source](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil)
after renaming the sender parameter, send expression, and architecture bind to
'cargo', and separately renaming the Server receive-pattern binder to the
same spelling 'cargo'. The actual
[production Haskell test](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs)
requires the two semantic identities to remain distinct and each unchanged
from the original checked source. Native replay must still succeed with exact
endpoint/payload transfer and affine spectator preservation.

**Negative controls:** Passing the sender's real semantic owner as the
externally authorized protocol receiver binder must produce exactly
'RestrictedMessageReceiverBinderMismatch'. Passing the receiver's semantic
binder as the externally activated sender owner must produce exactly
'RestrictedMessageOwnerMismatch', preserving occurrence, process and exact
expected/actual owners. These are adversarial *external authority premises*,
not source-invalid programs. Independently, changing only the sender
'close done' into 'close endpoint' in the jointly renamed complete source is
an executable **minimally rejected source witness**. It must produce exact
'GrammarV1ComponentSendCloseCloseMismatch', not an assurance/proof error.

[Six conditional Rocq 9.2 theorems](../../proof/Phil/Core/FSEM02DualBinderDisjointAuthority.v)
establish both mismatches/no-successor, both cross-impersonation refusals,
joint-success independent equalities and inherited exact ledger/frame
outcomes, and nonadmission of rejected source despite equal binders.
The [unprivileged focused GHC/Rocq workflow](../../.github/workflows/fsem02-dual-binder-disjoint-authority-preflight.yml)
checks native source/Core and proof witnesses before a broad CI PR.

**External inputs, trust premises and nonclaims:** Protocol family, message
boundary contract, role/process pairing, activation, selected root,
architecture population, exact owner/endpoint ledgers, scheduler, terminal
disposition and assurance remain independent. The conditional proof is
a functional owner-map abstraction and this source regression is finite
conformance, not universal source alpha-equivalence, implementation-to-Rocq
refinement, complete operational semantics, new source syntax or normative
FSEM-02 graduation.
