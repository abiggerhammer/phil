# FSEM-01 J-6A — distinct-owner Affine join groundwork

> **Reviewable groundwork only; non-normative.** This first J-6 tranche prepares a production source-join extension without editing `src/Phil/Surface/Check/Engine.hs`, which is currently allocated to the P9-F2 selected-provider correspondence lane. It does **not** claim that the regular Surface checker accepts this Affine join-state telescope, that a runtime phi selects a value, or that the nominal lifecycle premise has been discharged.

## Source fragment and independent authority

The existing parsed Grammar-v1 syntax can express one two-arm `if` with one explicit Affine `Permit` join-state slot and an invariant:

```phil
data Permit mode affine = Permit(U64);
fn choose(flag : Bool, permitA : Permit, permitB : Permit,
          payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state (selected : Permit) invariant true {
    permitA;
  } else {
    permitB;
  };
  return payload;
}
```

The checked lexical binding authority distinguishes `permitA`, `permitB` and fresh `selected` by source/declaration-rooted identities, not by equal types or display spelling. The first branch references exactly the first declared owner; the second references exactly the other. They do not carry the same moved source identity. A swapped-arm variant must retain both actual identities and reverse their order, not collapse them into one logical owner.

The **test-scoped**, source-only admission driver [Phase1FSEM01J6TwoAffineFoundationMain.hs](../../test/Phase1FSEM01J6TwoAffineFoundationMain.hs) uses the real `parseGrammarV1StructuralSource`, `grammarV1FunctionParameterScope`, `grammarV1CheckedJoinExpressionInScope`, exact local-value occurrences, `grammarV1CheckedClosedDataMode`, and `grammarV1CheckedTypeModeWithNamedResolutions`. It accepts only a nonrecursive, nongeneric function, two distinct externally admitted nominal `Permit` owners, a Bool flag and a Linear `Bytes[8]` spectator, an Affine `Permit` state slot and true/reflexive/unproved invariant form, and a source-bound return of the original `Bytes[8]` spectator. It does **not** project the checked branches into a production `SurfacePath`, call the Surface `checkValueBlock`, or bind the successor in `Engine.hs`; those are the explicit second-stage J-6B obligation.

**Nominal trust premise:** `data Permit mode affine = Permit(U64)` is strengthened from its derived unrestricted structural mode. The test supplies an existing `AdmittedLifecycleObligation` token, which is an **external admitted lifecycle justification**, not an independently proved permission to dispose of Permit. Both missing and explicitly unadmitted lifecycle justifications reject. The native input is not proof of lifecycle authority. Do not broaden this to all `TyOpaque` or assume Affine qualification.

## Distinct-owner Core move and join model

The same driver uses source-rooted checked names (never anonymous test names) to construct an actual native `Core.ResourceContext` with U flag, two different Affine owners, and one Linear `Bytes[8]` spectator. It independently calls production `Core.consumeAffine` on different owners for each static branch, observes the resulting asymmetric Affine maps, then calls `Core.joinContinuing`. The two unmatched source owners are absent from the intersection. It checks that `Core.insertBinding Affine selected Permit` succeeds only for a globally fresh slot, that both original names remain unusable, and that the final Linear spectator can be returned without unpaid linear debt.

Actual Core negatives include borrowed owner `OwnerBorrowed`, independently constructed live-loan `EscapingLoans`, unequal Linear/Unrestricted contexts, duplicate inserted slot, and stale consumed original owner. This is a **finite native Core run derived from checked source identities**; it is not the executed Surface production branch result nor an accepted whole source evidence record.

[Rocq J-6A foundation](../../proof/Phil/Surface/SurfaceTwoAffineJoinFoundationJ6.v) uses `Context`, `ContextJoin` and the earlier scoped Affine join bridge. Its theorems conditionally prove: a pointwise Affine move deletes only its selected owner; other Affine bindings and U/Linear/loan domains are unchanged; after the separately justified successful join, absent owners cannot reappear; insertion of a fresh Affine slot retains the owner absences; both branches' common Affine spectators are preserved; every Linear spectator survives; successful join and insertion remain loan-free; and duplicate Affine slot insertion rejects. These are kernel-checked **extensional model** properties, not an unconditional theorem of Haskell `Map`/`Set` behavior, source-control acceptance or runtime phi execution.

## Source controls, status and exact next handoff

The [18 source specimens](../../test/fixtures/fsem01-j6-two-affine-source-v1/) include accepted distinct owners, swapped arms and reflexive invariant, an explicit unproved false-invariant classification, a same-owner negative, wrong Bool operands and slot, active shadow, forward join-slot reference, omitted invariant/else, two-slot telescope, wrong return source/type, non-Bool condition, wrong nominal declaration mode and Linear data-payload mode weakening. **Out-of-adapter `Nothing` is not a normative invalid-source judgment**; a false logical invariant being classified as unproved is NOT a production `MissingEvidence` rejection before J-6B. Scope failures retain actual checker error constructors. One ordinary source program is not a proof of all Grammar-v1 `if` cases.

J-6A adds only this test driver, its original source fixtures, a Rocq proof module, this document, a focused nonprivileged preflight and precise phase-1 coverage/index notes. **No `Engine.hs`, `phil-core.cabal`, general source semantics, accepted grammar, TCB, P9 provider or FSEM-02 code changes.**

**J-6B later:** once P9-F2's checked-provider work releases the shared `Engine.hs` sites, add a separate narrowly authorized production `checkSurfaceSourceTwoAffineJoinComponent` source-to-resource bridge. It must independently verify real `checkValueBlock` branch values (not only lexical names), move and join both source states, introduce one fresh Affine slot with no duplicate or stale owner, establish exact accepted/rejected terminal state and error precedence including false-invariant `MissingEvidence`, and prove or test the actual Surface↔Core relation. It must return to a fresh exclusive `fsem-01` claim and protected CI/merge process. If P9's write ownership remains active, keep J-6B stopped rather than collide.

This work does **not** close general `JOIN-05` (dependent/multi-slot restricted telescopes), R10/R11/R15, arbitrary match/decide joins, universal native-to-Rocq correspondence, FSEM-05 source execution, FSEM-06 compiler realization, P8/P9/P10, release/assurance or Phase 1 freeze.
