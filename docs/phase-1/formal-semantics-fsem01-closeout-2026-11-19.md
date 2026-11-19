# FSEM-01 resource/local typing closeout reconciliation (2026-11-19)

**Status: OPEN — evidence audit and candidate work plan only, non-normative.**
Tracking: [#1613](https://github.com/abiggerhammer/phil/issues/1613).
Evidence cutoff: `main=b6154389d2ddb627ef92c7e32094ba785dd635ba` (2026-11-19 UTC);
exclusive `fsem-01` claim acquired before this work branch. The
[exit matrix](formal-semantics-fsem01-exit-matrix-v1.md) and
[COVERAGE-1](formal-semantics-fsem01-coverage1-v1.md) are historical
snapshots; this document supersedes only their dated status assertions.
Do not assert whole-language type soundness, implementation refinement,
source execution, or normative adoption from finite source/model tests.

## Reconciled merged evidence

| Rule family | Actual merged evidence | Still missing for general FSEM-01 exit |
| --- | --- | --- |
| R01–R03: lexical owners, mode and finite resource contexts | #1621/#1622, #1631/#1632, #1635–#1644, #1664/#1666; actual source/checker/finite models | Complete native `Text`/`Map`/`Set`–Rocq correspondence, Unicode and persisted declaration revision identity; external nominal Affine lifecycle attestation remains an independent premise |
| R04–R09: loan, completion, flat product, elimination | #1626/#1627, #1653/#1655/#1658/#1659, #1667/#1669/#1670; bounded source/Core/conditional Rocq | Recursive/nested/general record, sum, alias, projection and source-wide loan/ownership cases |
| R10/R11: joins and terminal branches | #1675/#1678/#1681/#1683/#1685, CORR-6 #1820, CORR-7 #1822, J-5 #1829, J-6A #1847 | J-6A distinct Affine source/Core identities are **not** a production Surface J-6B; multi-restricted/dependent telescopes, match/decide and general branch outcomes remain open |
| R12/R13: loops and closure captures | #1703/#1705/#1708/#1710/#1712 | Multi-slot loop/backedge, nonempty break, general capture graph, body and invocation owner effects |
| R15: tested source ↔ native/model finite cuts | CORR-1 #1718, CORR-2 #1813, CORR-3 #1815, CORR-4 #1817, CORR-5 #1819, CORR-6 #1820, CORR-7 #1822, CORR-8 #1853 | Universal Haskell-to-Rocq refinement, full-source error simulation and every-admitted-form correspondence |
| R08/R09/R14/R15: nested product | DATA-05A #1857, DATA-05B #1861, **DATA-05C #1864** (squash `4d0e08bad6d13418084436f006c9a147992578da`) | Only two mirrored two-level original patterns admitted; general recursive type/mode/elimination, arbitrary nested patterns and sealed source-byte provenance not shown |

**DATA-05C's exact limit:** original parsed `(Bool,(Bytes[8],Unit))`
and `((Bytes[8],Unit),Bool)`, original declaration-rooted leaf identities,
internally synthesized one Core name and two checked ordered product
contracts, two real Surface product eliminations, native predecessor and
successor resource snapshots, Linear completion and precise negative
observations. It does **not** justify unrestricted general product
typing, independent `satisfies C` discharge or global compiler correctness.

## The 20 baseline gap entries — current review dispositions

These are the **20 original #1712 baseline gap rows**, not 20 fresh PRs.
A row stays a general gap even if a narrower later fragment is proved.
An adapter returning `Nothing` means noncompetence, not invalid source.

| Row(s) | Remaining resource/local typing obligation |
| --- | --- |
| MODE-02 | Source records, recursive field modes and owner transfer |
| MODE-03 | Sum/variant payload modes and elimination |
| MODE-04 | Aliases, generic/recursive/dependent source types and modes |
| DATA-04 | General nested/recursive product type checking; narrow two-level #1864 only |
| DATA-05 | General nested/longer tuple-pattern elimination; #1864 covers two positional contracts only |
| DATA-06 | Record destructuring and owned-field binder restoration |
| DATA-07 | Restricted record/sum constructor payload move, copy, borrow and precise failure |
| DATA-08 | Field projection and owned/borrowed view error prefixes |
| LOAN-02 | Nested, multiple and reborrow lifetimes beyond single scoped paths |
| JOIN-05 | Restricted/dependent or multi-slot joins; #1829 Linear J-5 and #1847 Affine J-6A foundation are only partial |
| JOIN-06 | General source `match` arm owner joins/terminals |
| JOIN-07 | `decide` resource joins (proposition authority belongs to FSEM-04) |
| JOIN-08 | Case-pattern record/variant payload owner scopes and transitions |
| LOOP-05 | Mixed/dependent multi-slot loop state and invariant premises |
| LOOP-06 | Nonempty `break` actuals with exact exit resources |
| LOOP-07 | General multi-owner `continue`/backedge and scoped loans |
| CAP-03 | General closure bodies and multiple captures |
| CAP-04 | Source-derived recursive capture SCC graph instead of supplied graph |
| CAP-05 | Invocation callee ownership consume/preserve/replace (effects/authority FSEM-04) |
| TERM-02 | General typed reject/fail and source failure-prefix correspondence beyond CORR-8 |

The eight historical `handoff` rows remain assigned to the appropriate
family: FSEM-02 protocol, FSEM-03 architecture/root, FSEM-04 effect,
lifecycle and assurance, FSEM-05 executable Phase 1 source semantics
and independent extracted interpreter, and FSEM-06 source-to-target
realization. FSEM-07 separately owns normative graduation. No cross-family
claim is discharged by moving it out of this ledger.

## Parent #1613 acceptance criteria

| Criterion | Closeout finding | Required next proof/evidence |
| --- | --- | --- |
| 1. Exact rule, premises, state and failure | **Partial:** concrete bounded rules but missing general admitted shapes | For each gap settle accepted semantic domain; state rule/typing/diagnostic semantics or an actual adopted exclusion |
| 2. Accepted and minimally rejected *executable source* | **Partial:** many precise bounded tests | Add real positive/negative source pairs for still-admitted unsupported forms; do not mistake adapter noncompetence for invalidity |
| 3. Exact source/test/theorem/checked HEAD | **Established for named protected merges, not uncovered forms** | New evidence must pin exact source and checks, proof assumptions and merge SHA |
| 4. Stage, assumptions, TCB declared | **Explicit for bounded evidence; general claim unavailable** | Keep independent nominal attestation, concrete Haskell/Rocq relation and FSEM-04/05/06 dependencies separate |
| 5. No competing semantic-interface writers | **Active process gate** | Atomic exclusive `fsem-01` reservation before each work branch/PR, and P9 `Engine.hs` ownership respected |
| 6. No unsupported generalized proof or merge | **Observed for cited bounded slices; closure is still blocked** | Review every general row/authority decision, then update Logic Ledger, Conformance Matrix and parent checkbox only after evidence |

**Result: FSEM-01 remains unchecked.** The 46-row historical census
(18 `bounded`, 20 `gap`, 8 `handoff`) is a baseline, **not** a
completion percentage, a revised present-day count or a fixed PR budget.
Changing the canonical JSON classifications requires a new audited
evidence baseline and a deliberate update to its cutoff-enforcing validator.

## Next separate bounded implementation: DATA-04/05D

**Candidate, not authorized by this review-only PR.** After this PR is
merged and its claim is released, acquire a **new** `fsem-01` claim.
Extend [`SourceNestedProductElimination.hs`](../../src/Phil/Surface/GrammarV1/SourceNestedProductElimination.hs)
from two hardcoded two-level patterns to one additional **three-level**
source-derived nested pair fragment. Example original `.phil` specimen:

```phil
fn unpack(packet : (Bool, (Unit, (Bytes[8], Unit)))) -> Bytes[8] satisfies C {
  let (flag, (before, (payload, after))) = packet;
  return payload;
}
```

Acceptance requires all of:

1. Original parsed accepted/minimally rejected source pairs; exact
   declaration-rooted lexical binders, intrinsically checked leaf
   types/modes, declared return, and distinct original source owners.
   No aliases/generics/named proof authority silently admitted.
2. Internally derive **three ordered** product contracts and collision-free
   internal Core intermediate names from the checked *original source AST*.
   No caller-controlled `SurfaceEnvironment`, contract, privileged owner
   evidence or manufactured source binder. Run three unchanged real
   production Surface eliminations, with independently compared exact
   native `Map`/`Set` predecessor/successor resource states and unchanged
   spectator preservation.
3. Exact structural/mode/arity, shadow/duplicate, wrong return,
   stale-actor and failed-prefix controls. No post-failure invented
   successor, Linear owner resurrection, duplicated owner or unpaid
   terminal Linear debt. An unsupported source shape remains
   `Nothing`/noncompetence rather than a normative rejection.
4. Conditional Rocq finite tree/path/product preservation and
   no-resurrection theorems, compiled without new `Axiom`,
   `Parameter` or `Admitted`. Separately run actual source/native
   Haskell conformance; state all implementation/model assumptions.
5. A disjoint FSEM-01 adapter/test/proof/doc/preflight path set.
   Do not edit P9-owned `src/Phil/Surface/Check/Engine.hs` or
   FSEM-02, normative grammar, TCB, release/privileged workflows,
   independently owned assurance or provider/ABI code.
6. Strict GHC `-Wall -Werror` and Rocq 9.2 focused preflight;
   full exact-current-HEAD PR checks, fresh post-ready two-job claim
   guard, protected expected-HEAD squash, verified main readback and
   trusted exact claim release.

DATA-04/05D would establish one additional bounded shape; **it does not
close DATA-04 or DATA-05 generally**. Deeper recursion, broader primitives,
records, sums, aliases and dependent modes require independently justified
scope decisions and follow-up evidence. No runtime semantics (FSEM-05),
compiler refinement (FSEM-06), certified source byte identity or
`satisfies C` authority is implied by this finite adapter.

## Recommended remaining work order

1. Land this documentation-only reconciliation **without** ticking
   FSEM-01 complete. It must not overlap another `fsem-01` PR.
2. Then acquire a new claim for the bounded DATA-04/05D source adapter.
3. Keep J-6B production Affine Surface integration **stopped** until
   P9 explicitly releases shared `Engine.hs` write ownership; J-6A
   merged groundwork does not release it.
4. Disposition the remaining records/sums/aliases, nested loans,
   match/decide and mixed loops, recursive captures/invocation,
   general failure prefixes; seek explicit semantic-authority rulings
   where admitted semantics are genuinely underspecified.
5. Rebaseline COVERAGE-1, its machine validator, the Logic Ledger
   and Conformance Matrix only against reviewed proofs/tests and
   accepted scope decisions, then assess #1613's six criteria.
   Keep FSEM-04/05/06/07 and P8/P9/P10 obligations separate.

A passing CI suite proves those jobs passed on one immutable head.
A Rocq model proof proves its modeled theorem under stated premises.
Neither alone proves universal Haskell-to-Rocq or compiler refinement.
