# FSEM-02 restricted Send/Receive: typed terminal-head correspondence (non-normative)

Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613). This
bounded slice extends the source/owner and one-sided End-prefix observations
merged in #1721, #1722 and #1725. It does **not** widen the admitted fragment.

## Exact conditional judgment

Let `Σ₀` be the independently provided, activation-derived Core communication
state, `I` an independently admitted binary protocol instance with exact roles,
and `s,r` two separately parsed, checked two-statement Grammar-v1 component
bodies. Let `doneS,doneR` be **externally supplied** terminal outcomes; neither
source spelling nor successful close syntax manufactures that authority.

```text
Γ; I; Σ₀ ⊢ s.send(oldS,payload) / r.receive(oldR) ⇓ Σ₁
Σ₀.protocol[S,oldS].session = Send(b,Bytes[8],End(doneS))
Σ₀.protocol[R,oldR].session = Receive(b,Bytes[8],End(doneR))
Σ₀.linear[S,oldS] = TyEndpoint(original Send session)
Σ₀.linear[R,oldR] = TyEndpoint(original Receive session)
----------------------------------------------------------------
Σ₁.protocol[S,oldS] = absent; Σ₁.protocol[R,oldR] = absent
Σ₁.linear[S,oldS] = absent; Σ₁.linear[R,oldR] = absent
Σ₁.protocol[S,nextS] = (I,roleS,End(doneS))
Σ₁.protocol[R,nextR] = (I,roleR,End(doneR))
Σ₁.linear[S,nextS] = TyEndpoint(End(doneS))
Σ₁.linear[R,nextR] = TyEndpoint(End(doneR))
```

This is a **finite terminal-continuation** rule, not a general claim about
recursive or nonterminal sessions or text-to-name identity. A successful native
rendezvous is replayed from original state; the observer then independently
compares original checked source binder names, terminal head forms, exact
protocol metadata (including instance/role), consumed predecessors, and both
successor resource types. No cached transition or opaque default is accepted.

The production observer is
[`ComponentRestrictedTerminalHead.hs`](../../src/Phil/Surface/GrammarV1/ComponentRestrictedTerminalHead.hs).
Executable source witnesses in
[`Phase1FSEM02RestrictedSourceTransferMain.hs`](../../test/Phase1FSEM02RestrictedSourceTransferMain.hs)
include the admitted `Bytes[8]` source, the minimally rejected stale-close
fixture (`GrammarV1ComponentSendCloseCloseMismatch`), wrong original
sender session head (exact nested Core protocol rejection), consumed original
predecessor (exact restricted payload-owner mismatch), and a wrong supplied
terminal outcome (`RestrictedTerminalHeadOutcomeMismatch`). A `Left`
returns **no successor** and the original immutable value is not mutated.

[`FSEM02RestrictedTerminalHeads.v`](../../proof/Phil/Core/FSEM02RestrictedTerminalHeads.v)
proves that the conditional normalized transfer exposes no successor on a wrong
Send/Receive head or mismatched supplied terminal outcome; successful steps
have the exact source-authorized endpoint successors and receiver-owned
payload, with arbitrary other owner keys framed. These flags are premises, not
a proof that the whole Haskell source checker implements the Rocq relation.

Relation to [`SessionStep.v`](../../proof/Phil/Core/SessionStep.v):
continuation consumes the predecessor and inserts a fresh linear successor;
our concrete native observer checks the matching `TyEndpoint End` after
source replay. Relation to
[`ConcurrencySemantics.v`](../../proof/Phil/Core/ConcurrencySemantics.v):
the atomic synchronous restricted ownership transfer is a conditional
model. Neither file establishes full source-to-implementation refinement.

**Nonclaims:** no independent source-level architecture/root authority,
message admission, payload disposal, selected-root proof, assurance discharge,
general source-step semantics, fairness, parser soundness, extracted interpreter,
or normative graduation. Future FSEM-02/FSEM-05 slices must generalize beyond
the terminal-only continuations and relate all admitted constructs to an
independently executable semantics.
