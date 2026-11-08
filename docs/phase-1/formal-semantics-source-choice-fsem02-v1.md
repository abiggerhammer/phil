# FSEM-02 / source-selected choice with checked local successor (bounded v1)

**Non-normative production slice; not FSEM-02 completion.** Tracks
[#1613](https://github.com/abiggerhammer/phil/issues/1613). The prior bounded
[head-progression slice](formal-semantics-protocol-progression-fsem02-v1.md)
provides send/receive/close source-derived Ping and Core-only offer.

## Judgment, inputs, and rejection boundaries

```text
Σ[checked protocol family, instance revision, role] ;
Γ[source-resolved endpoint and successor occurrence] ;
Δ[Core resource map] ; P[live endpoint contract]
  |- let next = select LABEL on endpoint; close next
  ⇒ (P' at next = continuation(LABEL), Δ' without endpoint)
  | rejected(exact source binder error or ProtocolCheckError)
```

The source fragment is *only* a payload-free, unqualified `select LABEL on
endpoint` bound by an identifier followed by `close successor`. The
`Phil.Surface.GrammarV1.ComponentSelectClose` module checks the actual
parsed source's lexical endpoint, successor and close occurrence. It does
**not** mint protocol instance/role identity or infer an endpoint's type from
its spelling; these are explicitly supplied from a checked, closed, dual
protocol role projection and then checked by
`Phil.Core.Protocol.checkProtocolAction`. No longer form or opaque
fallback is silently accepted.

For the selected label `l`, the Core session must have a
`Select{l : S, ...}` head with a unique checked branch. Success consumes the
exact predecessor endpoint in **both** the protocol metadata and linear
resource map, installs a fresh source-named successor of `TyEndpoint S`
with the exact instance/role, and allows a terminal close only on `End
Done` (or that branch's specified outcome). Stale predecessor replay and
wrong head/instance reject. Missing labels reject as
`ProtocolSessionError (UnknownSessionLabel requested available)`.
A source `close endpoint` rather than `close successor` fails at the
binder checker with `GrammarV1ComponentSelectCloseCloseMismatch`.

The separate Core-only `ProtocolOfferRequest` is tested against the **same
source-derived server-role projection** with an explicitly supplied
external offerer's endpoint identity and label. This is a finite check of
matched local choice progressions, **not** source-level offer expression
elaboration or evidence of a network rendezvous.

## Witnesses and executable observations

`test/fixtures/fsem02-source-choice-v1/accepted.phil` is a whole parsed
program with a selected root, a closed dual `Choice` family, an internal
Client component, and an **external** Server role. The external provider's
admission/authority is not established here; this bounded test does not
certify the architecture or produce a physical peer.

`unknown-label.phil` differs only by `Go` → `Absent` at the source
select site. The parser and lexical adapter still recognize the same
source form; production Core rejects with exact label and available
branches. `stale-close.phil` differs only by the close operand
`chosen` → `endpoint`, which fails at source lexical comparison.
`test/Phase1FSEM02SourceChoiceMain.hs` tests all these paths, exact
linear predecessor deletion, fresh successor typing and identity,
terminal close, stale replay, wrong head, and wrong protocol-instance
rejection. Existing Ping send/receive tests remain separate.

## Rocq and proof limits

`proof/Phil/Core/FSEM02ProtocolHeadProgression.v` now includes
`FSEM02Select` with computable label lookup, explicit missing-label /
wrong-head rejection, the exact predecessor/successor resource theorem
specialized to select, and a conditional **local** select/offer resource
comparison on identical admitted branch catalogs. The theorem about
matched local heads does not imply dual endpoint ownership, branch
coverage, protocol-instance authenticity, communications, or rendezvous.
The historical `SessionStep.endpointType` remains an abstract token,
not a proof of Haskell `TyEndpoint` equality.

**Remaining obligations:** checked source offer expression, branch-total
source ownership, general payload-bearing select/offer, restricted message
transfer through an actual checked rendezvous, external role provisioning
evidence, universal source/Haskell↔Rocq correspondence and FSEM-02 exit.
No `Admitted`/`Axiom`/`Parameter`, normative grammar, TCB, or language
authority is added by this slice. The tests establish finite conformance,
not compiler correctness, fairness, progress or liveness.
