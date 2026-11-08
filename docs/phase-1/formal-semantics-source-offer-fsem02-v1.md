# FSEM-02 / source offer catalog totality (bounded v1)

**Non-normative; FSEM-02 remains open.** Follows
[checked source select](formal-semantics-source-choice-fsem02-v1.md) and tracks
[issue #1613](https://github.com/abiggerhammer/phil/issues/1613).

## Exact admitted fragment and authority inputs

The production `ComponentOfferCoverage` adapter reads a complete parsed
Grammar-v1 component whose body is *only* the expression

```phil
offer endpoint {
  Go => { return unit; }
  Cancel => { return unit; }
};
```

The endpoint must resolve to a true source component parameter. Each arm must
have an unqualified label, **no** tuple/record binders, and one block-local
`return unit` statement. This is a structural/coverage-only fragment, not an
executable per-arm protocol continuation. An unrecognized source shape yields
`Nothing`, **not** successful checking.

**Inputs:** a separately closed and dual-checked binary protocol family and
an actual `ProtocolProjectionEvidence` from
`Phil.Core.Protocol.Family.projectProtocolRole`. The adapter requires that
projection's session head to be `Offer branches`, verifies duplicate-free
source arms, and checks exact bidirectional branch-label coverage. There is
no guessed role, nominal endpoint authority, or implicit external admission.
Neither the named component parameter's written type nor architecture
provisioning is proved to correspond universally to that projection.

## Judgment and failures

```text
Σ[checked instance/role projection] ; Γ[parsed component binder scope]
|- offer e { l1 => return unit; ... ln => return unit; }
   : covers(Offer{l1:S1,...,ln:Sn})
  | rejected(unbound/nonparameter e, non-Offer head,
             unsupported binder/body, duplicate/missing/extra arm).
```

Coverage does not consume `e`, produce an endpoint successor, evaluate an
arm, or close a session. This distinction is deliberate: source offer syntax
and its continuation binding/terminal obligation require further semantics.

The full parsed fixtures in `test/fixtures/fsem02-source-offer-v1/` include
a checked Server role offer with two arms and a selected root program.
`missing-arm.phil` deletes only the Cancel arm and rejects **exactly**
`GrammarV1ComponentOfferMissingArm "Cancel"`. Duplicate Go and unbound
operand cases reject their own explicit classes. The Haskell executable
`test/Phase1FSEM02SourceOfferMain.hs` checks both local Core offer labels
separately with `checkProtocolAction`, exact predecessor consumption, typed
successors, stale replay failures, and terminal cleanup. Those Core local
actions are **not** inferred to be execution of either source return-unit arm.

`proof/Phil/Core/FSEM02ProtocolHeadProgression.v` adds a finite branch-label
model and conditional theorems: given extensional catalog equality and
no-duplicate source labels, each source label has a modeled local continuation,
and a missing arm prevents coverage. The existing SessionStep/ConcurrencySemantics
dependencies are unchanged, and no Haskell-to-Rocq simulation is established.

**Still open:** complete source offer body typing and continuation binding,
branch-local owner cleanup, selected-label network rendezvous and scheduler
choice, payload transfer and restricted-resource transfer, architecture role
admission, exact general source/implementation simulation, FSEM-02 completion,
and eventual normative review. No new `Axiom`, `Parameter`, `Admitted`,
TCB amendment, or normative syntax change belongs to this slice.
