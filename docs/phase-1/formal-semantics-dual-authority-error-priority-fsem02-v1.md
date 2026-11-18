# FSEM-02: simultaneous source, activation-owner and protocol-binder diagnostic priority

**Status: bounded, non-normative; FSEM-02 incomplete.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This is *diagnostic precedence*, not another independent binder equality test or another fault-mask count. It adds no grammar, TCB or privileged-workflow authority.

## Partial decision and independent premises

For the already checked restricted \`send Bytes[8]\`/\`receive Bytes[8]\` rendezvous fragment, consider a source Close operand \`c\`, source-written receiver type \`t\`, checked declaration-rooted sender and receiver identities \`b_s,b_r\`, and **independently supplied** activation owner \`a_s\` and authorized protocol binder \`p_r\`. The specific tested decision chain is:

\`\`\`text
invalid source Close operand          -> GrammarV1ComponentSendCloseCloseMismatch
valid Close; wrong receive type       -> RestrictedSourceMessageTypeMismatch
valid source; b_s != a_s              -> RestrictedMessageOwnerMismatch
valid source and owner; b_r != p_r     -> RestrictedMessageReceiverBinderMismatch
all four gates pass                   -> proceed to other Core checks (not automatic success)
\`\`\`

The production source adapter checks the two parsed component bodies and written payload types before calling the existing Core checker. The Core restricted-message transfer validates the exact activation-owned sender occurrence **before** the receive-message binder contract. Thus two simultaneous external forgeries must report the earlier owner mismatch; repairing only that forgery exposes the remaining protocol-binder mismatch, never a successful state. This priority is an observable error contract for these specific cases, **not** a universal ordering of every possible source/Core error. In all refusal cases the pure checker returns \`Left\`, with no successor state.

## Actual parsed source, positive and precise negatives

The complete [accepted source](../../test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil), production [Haskell regression](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs) and existing external generic protocol/activation fixture jointly execute: (1) sender-owner forgery plus independent mismatched protocol receiver binder; exact first \`RestrictedMessageOwnerMismatch\` fields; (2) restore only original owner; exact exposed \`RestrictedMessageReceiverBinderMismatch\`; (3) restore both independent authorities; accepted native restricted transfer with exact endpoint successors, linear payload transfer and affine spectator frame.

The minimally rejected whole-source specimen changes **only** sender \`close done\` to \`close endpoint\` (same source artifact, parsed anew); it must reject as \`GrammarV1ComponentSendCloseCloseMismatch\` **even while both external authorities are forged**. An independent single receive-type change \`Bytes[8]\`→\`U8\` must reject as \`RestrictedSourceMessageTypeMismatch(Bytes[8], U8)\` before those external defects. Neither negative creates a successful successor or silently translates a proof obligation into an invalid-language verdict.

[Six conditional Rocq 9.2 classifier theorems](../../proof/Phil/Core/FSEM02DualAuthorityErrorPriority.v) prove these four-gate priority facts, plus that a modeled \`ReadyForCore\` decision entails valid Close, valid written type and both exact identity equalities. \`ReadyForCore\` is **not** a proof of actual Core transfer or a replacement for the pre-existing conditional owner-ledger theorem in [dual binder disjoint authority](formal-semantics-dual-binder-disjoint-authority-fsem02-v1.md). [Focused verification](../../.github/workflows/fsem02-dual-authority-error-priority-preflight.yml) runs strict GHC and source/native witnesses plus admission-free Rocq proofs.

**Explicit external premises / nonclaims:** Protocol family and instance/roles, boundary message contract, architecture activation, owner occurrence, live endpoint heads, selected root, scheduler, terminal dispositions and assurance remain separate. This covers finite production Haskell error precedence and a proof-side classifier, **not** the classifier's universal refinement by Haskell, completeness of Phase 1 source semantics, globally fixed error priorities, compiler verification, or normative graduation.
