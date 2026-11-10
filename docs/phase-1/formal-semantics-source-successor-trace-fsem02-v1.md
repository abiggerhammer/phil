# FSEM-02: restricted source successor-identity trace (bounded v1)

**Non-normative; FSEM-02 incomplete.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). This distinct follow-up to [#1721](https://github.com/abiggerhammer/phil/pull/1721) records the *complete original-predecessor → rendezvous successor → two End closures* owner-identity correspondence; it does not change the Phase 1 grammar, TCB, admitted protocol authority or normative semantics.

## Admitted partial judgment and explicit inputs

For the parsed, exact two-statement Grammar-v1 send/close and receive/close components, with explicit declaration roots, externally admitted restricted `Bytes[8]` message boundary/protocol instance, activation-derived network and communication predecessor `Σ₀`, distinct sender/receiver/payload activation occurrence keys, externally selected roles and process identities, and independently authorized terminal outcomes:

```text
source, Σ₀, external instance/roles/occurrences/End outcomes
    -- production restricted send/receive --> Σ₁
    -- sender then receiver End --> Σsr
    -- receiver then sender End --> Σrs
accept iff full Σsr = Σrs, the source-resolved owner trace matches,
  and all unmentioned occurrence owners are unchanged.
otherwise exact typed source/Core/trace rejection; no successful successor.
```

The production `grammarV1CheckRestrictedSourceSuccessorTrace` replays `grammarV1CheckRestrictedSourceCloseDiamond` from **original** `Σ₀`; it does **not** trust a cached carrier or re-infer nominal authority from syntax. Its separate finite owner observation explicitly checks the original source-resolved sender endpoint, receiver endpoint and linear payload owners; exact post-rendezvous successor identities and payload transfer; full-map spectator frame; and exact endpoint-occurrence deletion after **both** close orders. It requires distinct externally named occurrence keys. A failure returns a precise `RestrictedSuccessorTrace*` constructor with no successor. The native Core checks remain authoritative for live `TyEndpoint`, send/receive head compatibility, resource consumption, fresh successor insertion and End outcome.

## Executable positive and minimal negative evidence

`test/Phase1FSEM02RestrictedSourceTransferMain.hs` runs the full parsed `test/fixtures/fsem02-restricted-source-transfer-v1/accepted.phil` through the production adapter. It compares the independently executed diamond and exact complete occurrence maps before, after the rendezvous, and after both closures, including the transferred receiver-owned payload and independent affine spectator.

It separately alpha-renames the source sender's `done` *display spelling* to `successor` with its corresponding close expression, re-parses/rechecks the program, and checks that the **one admitted declaration-rooted ordinal identity** and resulting native owner traces remain identical. This is a concrete source witness, not a general alpha-equivalence proof. The minimally rejected `rejected-stale-close.phil` changes only the sender's `close` operand; it must reject with the nested exact class `GrammarV1ComponentSendCloseCloseMismatch`. Additional adversarial executions reject a fabricated external sender occurrence as `RestrictedSuccessorTracePredecessorMismatch` and an aliased sender/payload occurrence as `RestrictedSuccessorTraceAliasedOccurrence`. The pre-existing suite continues checking wrong session heads, stale predecessor state, duplicate owner/resource and wrong terminal outcomes.

## Conditional Rocq correspondence / exact limit

`proof/Phil/Core/FSEM02RestrictedSuccessorTrace.v` composes **existing** `FSEM02RestrictedSourceTransfer.v`'s explicit predecessor→successor/payload/frame rule with `FSEM02RestrictedCloseDiamond.v`'s conditional two-order owner-retirement theorem. Given source/message/head admission and **successful** transitions of both externally authorized closure orders, it establishes exact endpoint successor identities before closure; exact deletion after closure; payload ownership transfer and persistence; framing from the **original** ledger (not just the post-transfer state); and pointwise equality of both final ledgers. Additional lemmas reject a reused retired sender occurrence and unaccepted source. `SessionStep.v` and `ConcurrencySemantics.v` continue to supply separate abstract local resource/protocol and restricted-rendezvous premises.

There is **no** universal Haskell`Map`↔Rocq functional-map refinement, parser soundness, general alpha-equivalence theorem, executable Rocq source interpreter, global progress/deadlock/fairness/termination theorem, or derived protocol admission. Activation ownership, selected root, role and terminal dispositions, resource disposal, may-effects, obligations and assurance remain external. The finite conditional theorem does **not** promote normative Phase 1 semantics or close FSEM-02.

Focused work-branch preflight: `.github/workflows/fsem02-source-successor-trace-preflight.yml` (warning-free Haskell build and executable source/native tests; Rocq 9.2 proof compilation/no new admissions). Broad exact-head checks, ready-for-review claim guard and protected merge remain separate gates.
