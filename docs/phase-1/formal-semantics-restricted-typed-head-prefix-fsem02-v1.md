# FSEM-02 — typed restricted Send/Receive head to one-sided End-prefix composition

**Status: non-normative, bounded and subject to exact-head verification.** Tracks
[issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
This slice composes the independently tested [terminal head rule](formal-semantics-restricted-terminal-heads-fsem02-v1.md)
and [both first-End owner prefixes](formal-semantics-restricted-close-prefix-ledgers-fsem02-v1.md);
it does not extend the admitted Grammar-v1 language or create source-derived disposal authority.

## Exact judgment and witnesses

Let `Σ₀` be the independently supplied original activation-derived process
communication state, `I` the separately admitted binary restricted-message
instance and matching roles, `s/r` two independently checked source bodies,
`ocS/ocR/ocP` three **distinct** externally supplied activation occurrence
keys, and `doneS/doneR` separately authorized End outcomes.

```text
Γ; I; Σ₀ ⊢ s.send / r.receive ⇓ Σ₁ : typed End(doneS), End(doneR)
Σ₀ ──independent source/native replay──▶ Σ₁' ; require Σ₁ = Σ₁'
Σ₁ ──authorized End(sender)──▶ Σs
Σ₁ ──authorized End(receiver)──▶ Σr
--------------------------------------------------------------------
Σs: sender endpoint absent, receiver typed End still live
Σr: receiver endpoint absent, sender typed End still live
Σs.owner(ocP) = Σr.owner(ocP) = receiver's source-resolved payload binder
other affine/linear spectators unchanged; error ⇒ no valid successor
```

Production `ComponentRestrictedTerminalHead.grammarV1CheckRestrictedTypedPrefixTrace`
executes **two separate replays from the original state** and compares the
complete Core communication state before examining both actual first-End
states. It independently verifies that the remaining endpoint retains its
exact instance/role/End state in *both* protocol and linear resource maps.
The underlying prefix adapter requires complete activation owner-ledger
equality, payload transfer, spectators and both final close orders. Neither
source spelling nor a cached native transition is accepted as terminal authority.

The parsed accepted `Bytes[8]` fixture is
`test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil`.
The one-operand minimally rejected
`rejected-stale-close.phil` must produce the exact nested
`GrammarV1ComponentSendCloseCloseMismatch` source error.
`test/Phase1FSEM02RestrictedSourceTransferMain.hs` also checks deterministic
replay, independently reproduced transitions, a wrong supplied End outcome
(`RestrictedTerminalHeadOutcomeMismatch`), a wrong original sender head
(`RendezvousProtocolError`), consumed-predecessor/payload replay
(`RestrictedMessageOwnerMismatch`), and aliased external endpoint
occurrences (`RestrictedSuccessorTraceAliasedOccurrence`). No generic
build failure is accepted as the expected rejection.

`proof/Phil/Core/FSEM02RestrictedTypedHeadPrefix.v` proves conditional
composition of the existing `FSEM02RestrictedTerminalHeads.v` gate and
`FSEM02RestrictedClosePrefixLedgers.v` owner/payload/spectator/terminal
diamond. It also proves no successor for incorrect Send or Receive heads.
These proofs reuse the abstract predecessor/successor rules of
`SessionStep.v` and conditional synchronous transfer of
`ConcurrencySemantics.v` through existing imported models.

**External trust premises:** authorized protocol instance, exact roles,
boundary message contract, payload activation occurrence, source binder
resolution, activated network, three distinct occurrence keys and two
independent legal End-disposal outcomes. No Haskell-to-Rocq universal
simulation, terminal source authority, admitted nonterminal/recursive
session semantics, scheduler/fairness, root/assurance validity, or normative
graduation is proved. FSEM-02 remains open.
