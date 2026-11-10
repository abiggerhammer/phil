# FSEM-02 restricted send/receive one-sided terminal owner ledgers

> **Non-normative, bounded source/Core/Rocq correspondence.** This slice does
> not authorize endpoint disposal, admit a root architecture, or prove
> universal Haskell-to-Rocq refinement. It follows #1722 and #1724.

## Exact partial rule and authority

Let Σ₀ be the **original activated** Core communication state with three
distinct, externally named activation occurrences S (sender endpoint),
R (receiver endpoint), and P (restricted payload), plus arbitrary affine
spectators X. The parsed, source-checked Grammar-v1 send/receive program
supplies exact declaration-rooted predecessors `s₀,r₀,p₀` and successors
`s₁,r₁,p₁`. The **external**, separately admitted `BinaryProtocolInstance`,
boundary certificate, role/process identities, activation, session-head
validity and authorized End outcomes are explicit inputs, not derived from
the source spelling or `Bytes[8]` syntax.

```text
Σ₀: owners[S]=(sender,s₀), owners[R]=(receiver,r₀),
    owners[P]=(sender,p₀), owners[X]=(spectator,...)
source send/receive + externally admitted protocol/heads
  -- actual Core synchronous restricted rendezvous --> Σ₁
Σ₁: owners[S]=(sender,s₁), owners[R]=(receiver,r₁),
    owners[P]=(receiver,p₁), owners[X] unchanged
Σ₁ -- externally authorized sender End --> ΣS
Σ₁ -- externally authorized receiver End --> ΣR
ΣS.owners = Σ₁.owners \\ {S},   ΣR.owners = Σ₁.owners \\ {R}
ΣS -- authorized receiver End --> ΣSR
ΣR -- authorized sender End --> ΣRS
accept only if native ΣSR == ΣRS (all Core state collections).
```

The new production
[`grammarV1CheckRestrictedSourceClosePrefixes`](../../src/Phil/Surface/GrammarV1/ComponentRestrictedSourceClose.hs)
**independently replays** the original source/predecessor via the
source-successor trace checker, then independently invokes the real
`closeProcessEndpointState` for the sender-first prefix. It checks the
*entire* restricted-owner maps of both prefixes against the independent
exact-one-occurrence deletions from Σ₁. The earlier diamond still
compares the *complete* final Core states, rather than just the ledger.
The payload and arbitrary spectators survive in both prefixes.

The deterministic executable
[`Phase1FSEM02RestrictedSourceTransferMain.hs`](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs)
replays actual source and Core transitions twice. It exercises accepted
`Bytes[8]` send/receive with final sender/receiver-owned endpoint states,
the transferred linear payload, and an unrelated affine spectator. It also
checks a **minimally rejected** complete source
[`rejected-stale-close.phil`](../../test/fixtures/fsem02-restricted-source-transfer-v1/rejected-stale-close.phil)
with exact `GrammarV1ComponentSendCloseCloseMismatch`, source replay
from a consumed predecessor with `RestrictedMessageOwnerMismatch`, wrong
receiver End outcome with `CloseOutcomeMismatch`, and repeats of both
retired endpoint closes with exact `EndpointClosureOccurrenceUnknown`.

Rocq 9.2
[`FSEM02RestrictedClosePrefixLedgers.v`](../../proof/Phil/Core/FSEM02RestrictedClosePrefixLedgers.v)
composes the existing normalized
[`FSEM02RestrictedSourceTransfer.v`](../../proof/Phil/Core/FSEM02RestrictedSourceTransfer.v),
[`FSEM02SelectedClientClose.v`](../../proof/Phil/Core/FSEM02SelectedClientClose.v),
[`FSEM02ExplicitPeerClose.v`](../../proof/Phil/Core/FSEM02ExplicitPeerClose.v)
and [terminal diamond](../../proof/Phil/Core/FSEM02RestrictedCloseDiamond.v).
Conditional theorems prove exact one-sided retirement, continued opposite
endpoint and transferred-payload ownership, original spectator framing,
commuting final owner ledgers, and modeled repeated-retirement refusal.

**Nonclaims:** no source-derived Server End/disposal authority; no assumption
that successful local closes discharge the linear payload, root terminal
facts or assurance obligations; no general stuck-state/scheduler semantics,
fairness, parser/compiler correctness, native map-to-Rocq representation
refinement, normative language graduation or end-to-end theorem. Refer to
[SessionStep.v](../../proof/Phil/Core/SessionStep.v) and
[ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v)
for their established abstractions and boundaries.
