# Phase 0 Phil Core Judgments

This document is normative for the first Phil Core checker-facing semantics.

It instantiates ADR-001 against the accepted upload demonstrator and the decisions in ADR-002, ADR-003, ADR-004, ADR-005, and ADR-006.

## 1. Static and resource contexts

The checker operates relative to:

```text
Σ ; Γ ; A ; Δ
```

where:

- `Σ` — immutable declarations/contracts: types, modes, grammars, protocols, claims, primitives, validators, obligation boundaries;
- `Γ` — unrestricted values/evidence/declarations;
- `A` — affine owners/capabilities, usable at most once;
- `Δ` — linear owners/lifecycle resources, usable exactly once.

Shared-loan bookkeeping is internal checker state associated with an owner in `A` or `Δ`; it is not a fourth structural mode.

## 2. Normative provider judgment

```text
Σ ; Γ ; A ; Δ ⊢ P :: (c : S) ▷ Φ
```

means that `P` provides `c : S` while respecting structural/session/evidence rules and generating named residual obligations `Φ`.

For the upload server, the provided interface is conceptually:

```text
server : Endpoint[ServerUpload]
```

and every session action consumes one endpoint state to obtain the declared successor state or terminal resource transition.

## 3. Bidirectional value checking

A practical checker uses:

```text
Σ ; Γ ; A ; Δ ⊢ e ⇒ T ⊣ A' ; Δ' ▷ Φ
Σ ; Γ ; A ; Δ ⊢ e ⇐ T ⊣ A' ; Δ' ▷ Φ
```

The arrows `⇒` and `⇐` mean synthesize and check.

Residual resource contexts make consumption explicit:

```text
x : U in Γ
    use x
    -> x remains in Γ

cap : AType in A
    consume cap
    -> cap absent from A'

endpoint : Endpoint[S] in Δ
    send/select/receive/offer/close endpoint
    -> old endpoint absent from Δ'
       successor inserted when the operation has one
```

A failed transport operation whose contract returns no successor does not reinsert the consumed endpoint.

## 4. Process/control checking

Conceptually:

```text
Σ ; Γ ; A ; Δ ⊢ P ⇝ K ⊣ A' ; Δ' ▷ Φ
```

with:

```text
K ::= Continue
    | Return(r : R)
    | Closed(outcome)
    | Failed(class, detail)
```

Continuing/returning paths carry residual resources. Terminal `Closed`/`Failed` paths carry no continuing linear residue.

This is the checker-side form of ADR-003's rule that terminal branches do not create dummy endpoints in order to join a continuing branch.

## 5. Sequential composition

Checking proceeds left-to-right through explicit program order.

If:

```text
Σ ; Γ ; A0 ; Δ0 ⊢ P1 ⇝ Continue ⊣ A1 ; Δ1 ▷ Φ1
Σ ; Γ ; A1 ; Δ1 ⊢ P2 ⇝ K        ⊣ A2 ; Δ2 ▷ Φ2
```

then conceptually:

```text
Σ ; Γ ; A0 ; Δ0 ⊢ P1 ; P2 ⇝ K ⊣ A2 ; Δ2 ▷ (Φ1 ∪ Φ2)
```

A terminal first statement has no sequential continuation.

Obligation IDs are stable; set/collection union above does not erase origin or scope metadata.

## 6. Local branching

Every branch begins from the same incoming resources because only one branch executes.

Each branch is checked independently.

For continuing branches:

- corresponding linear residues must be definitionally equal;
- affine residue may be conservatively forgotten if absent from any continuing branch;
- unrestricted bindings remain reusable.

Terminal branches contribute no continuing residue.

This rejects the incompatible-branch-join witness even when both arms are individually legal.

## 7. Session head checking and polarity

Phase 0 head polarity is:

```text
positive:
    !
    ⊕

negative:
    ?
    &

terminal:
    end[o]
```

A positive session state requires an explicit local action/choice.

A negative state determines the permitted receive/offer structure but still performs a runtime communication action; "negative" does not mean nonblocking.

Guarded recursion is unfolded only enough to expose the head constructor for checking/equality.

## 8. Send / ownership transfer

For:

```text
e : Endpoint[!(x : M).S(x)]
```

sending a value `v : M` consumes `e` and uses `v` according to `M`'s structural mode.

If `M` denotes a linear owner such as exact payload bytes, the send contract transfers ownership: the sender no longer owns `v` after successful transfer.

If `M` is unrestricted, ordinary reuse remains legal.

On transport failure, ownership follows the primitive's ADR-005 failure contract; the checker does not infer it from the error class alone.

## 9. Grammar-backed receive

For:

```text
e : Endpoint[?(x : Frame[G]).S(x)]
```

a split implementation checks:

```text
receive_frame(e)
    -> pending : PendingRecv[...]        [linear]

borrow pending as raw : RawBytes[id] {
    recognize G raw
        -> parsed : Parsed[G,id,value]
         | RecognitionFailure[G]
}
```

No `Endpoint[S(value)]` is in `Δ` yet.

After the loan ends:

```text
commit_receive(pending, parsed)
    -> e' : Endpoint[S(value)]
```

requires matching frame/provenance identity and consumes `pending`.

On recognition failure:

```text
fail recognition(reason) on pending
```

consumes the pending owner and yields terminal failure, not a successor endpoint.

## 10. Refined value checking

For a refined type:

```text
{x : T | P(x)}
```

the value must first check as `T`, and the checker must discharge or legitimately residualize `P(value)` according to ADR-006.

A successfully received refined message establishes local evidence for its declared refinement.

A chooser-local prerequisite attached to a bare protocol label is not automatically receiver evidence.

## 11. Evidence use

Given:

```text
evidence : Proof[P]
```

or specialized evidence that entails `P`, `using evidence` may discharge a requirement for exactly the matching proposition, modulo permitted definitional equality.

Context/subject identities are part of matching where declared.

Thus:

```text
Validated[BeginPolicy, κ1, begin]
```

does not satisfy:

```text
BeginPolicy(κ2, begin)
```

without checked evidence relating `κ1` and `κ2`.

Opaque claims such as `DigestMatches` cannot be introduced by generic `prove`.

## 12. Propositional transport

Definitional equality is intentionally small.

When:

```text
p : Proof[a == b]
x : T[a]
```

an explicit checked transport may produce:

```text
transport x using p : T[b]
```

For a linear `x`, transport preserves unique ownership:

```text
x : T[a] in Δ
    -> transport consumes the source typing occurrence
    -> one owner of T[b] in the successor Δ
```

No duplicate owner is created.

This is the required mechanism behind examples such as converting `Bytes[4096]` to `Bytes[begin.length]` when, and only when, equality evidence actually exists.

## 13. Shared loan checking

Conceptually:

```text
borrow owner as view {
    P
}
```

marks `owner` as shared-borrowed for the lexical scope.

Inside the scope:

- read operations through `view` are legal;
- `view` may be copied/discarded inside its lifetime;
- owner-consuming/moving/releasing/mutating operations are unavailable.

At scope exit:

- `view` cannot escape;
- owner becomes available again in its original structural zone.

This types both client-side hashing before transfer and server-side digest checking before `release`/`store`.

## 14. Obligation generation

Operations may append named obligations to `Φ`.

Representative upload obligations include:

```text
upload.hello.policy
upload.version.offered
upload.version.unsupported_disjoint
upload.begin.policy
upload.payload.exact_length
upload.digest.matches
```

The exact ID naming convention may be hierarchical, but IDs must be stable under deterministic re-elaboration of unchanged architecture/source identity.

At each required point ADR-006's canonical discharge order applies.

The checker hands each generated obligation revision and every successful static-discharge mechanism to ADR-010's assurance pipeline with stable identity, canonical proposition, origin/scope, and required point. Runtime-bound/exported obligations carry the declared boundary/mechanism rather than being silently treated as proved.

The assurance-ledger verifier, not the ordinary expression checker, decides whether a particular build manifest has a closed acceptable assurance graph. `Φ` is therefore the checker-to-ledger interface rather than the ledger itself.

## 15. Focusing / canonical elaboration

The checker performs deterministic work without agent-visible branching:

```text
normalize
resolve mode
unfold transparent claims
expose guarded session head
insert canonical UInt->Nat index coercion
check branch exhaustiveness
use matching in-scope evidence
invoke configured certificate-checkable transparent solver
```

It never focuses by guessing:

```text
which protocol label to select
which runtime validator to insert
which assumption to make
which opaque claim to accept
which obligation boundary to cross
```

Those are explicit architecture/program choices.

## 16. Complete-component acceptance

A complete Phase 0 component is accepted when:

1. all source constructs elaborate deterministically to Core;
2. the declared result/interface checks;
3. every linear owner is consumed or transferred exactly once;
4. every affine owner is used at most once;
5. no loan escapes;
6. every session action matches the current endpoint state;
7. every required proposition has matching evidence or an explicitly permitted residual disposition;
8. all continuing branch joins have compatible residues;
9. all terminal branches discharge their branch-local linear resources;
10. every residual obligation emitted for the component has a stable ADR-010 handoff record and an architecture-permitted disposition.

## 17. Conformance witnesses

The following corpus families exercise the judgment boundary:

- consumed/dropped endpoints -> structural/session checking;
- nonexhaustive offer -> negative session checking;
- incompatible join -> residual-context join checking;
- raw/parsed/validated misuse -> evidence/type checking;
- wrong pending-frame evidence -> stable-identity matching;
- copied payload / dropped pending receive -> structural modes;
- escaped loan -> lifetime checking;
- stale policy evidence -> context-specific proposition matching;
- opaque digest proof attempt -> evidence-introduction competence;
- branch-label proof fabrication -> communication/evidence boundary;
- unchecked wraparound -> mathematical refinement semantics.

Two independent Phil Core checkers should reject each witness at the same earliest competent semantic layer, even if their diagnostics are worded differently.
