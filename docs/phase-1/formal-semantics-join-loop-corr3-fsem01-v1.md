# FSEM-01 CORR-3: finite four-zone source-cut to Rocq model relation

> **Provisional non-normative review slice.** Parent [#1613](https://github.com/abiggerhammer/phil/issues/1613).
> Follows protected [CORR-1 #1718](https://github.com/abiggerhammer/phil/pull/1718)
> and [CORR-2 #1813](https://github.com/abiggerhammer/phil/pull/1813).
> Neither passing finite tests nor conditional theorems establish universal Haskell↔Rocq refinement,
> complete FSEM-01, FSEM-05/06, P10 final authority or Phase 1 freeze.

## Missing boundary addressed

CORR-2 independently replayed actual checked source joins and one-slot Linear loop prefixes
through production Core operations, but its Rocq results were conditional on extensional
Core contexts. CORR-3 makes the **finite resource-context representation premise explicit**
at every reached source-derived cut and composes it with those existing model laws.

The unchanged source producers are
[SourceScopedBorrowJoin](../../src/Phil/Surface/GrammarV1/SourceScopedBorrowJoin.hs)
and [SourceLinearLoopTransfer](../../src/Phil/Surface/GrammarV1/SourceLinearLoopTransfer.hs).
No grammar, compiler, source-checker acceptance policy or normative semantics changes.

## Native evidence and negative cuts

The new [strict native driver](../../test/Phase1FSEM01Corr3FiniteProjectionMain.hs)
re-parses **11 real accepted and rejected Grammar-v1 specimens** from
J-1/J-2 and L-2/L-3. It extracts every reached checker checkpoint,
including join branch/loan and error prefixes, loop owner move,
header/backedge/reentry and scoped loan transitions.

For each checkpoint it checks canonical finite projections of all four
resource collections: unrestricted Γ, affine A, linear Δ and active shared
loans. It rejects unsorted or duplicate keys across zones, orphan loans
and noncanonical loan order *before* reifying a finite representation into
Haskell Map/Set. It compares the resulting full state to the actual source
checker observation, then uses an independent finite-list lookup to
verify all observed names plus absent probes. The unchanged CORR-2 driver
also replays real Core operations and precise source failure stages.

Nine adversarial controls reject duplicate/omitted/cross-zone owners,
orphan or fabricated loans, reversed two-owner ordering, wrong checked
type, and spurious unrestricted/affine entries. An unsupported adapter
fragment is not treated as a normative source-language rejection.

These are **finite native conformance tests**, not an extracted
reference checker, a proof of unbounded Haskell Map/Set semantics
or a cryptographic provenance guarantee.

## Formal correspondence and precise limit

[SurfaceSourceJoinLoopCorr3.v](../../proof/Phil/Surface/SurfaceSourceJoinLoopCorr3.v)
uses the proved
[ExactFiniteRelation](../../proof/Phil/Surface/SurfaceFiniteContextFrame.v)
between every finite U/A/L/loan lookup and a supplied Rocq
Context.ResourceContext, not merely counts or selected membership bits.

Its conditional Rocq 9.2 theorems cover:

1. Exact finite source-owner preservation and closed loans across both
   continuing join predecessors and the joined context.
2. Preservation of the **whole finite linear lookup domain** on a
   successful two-predecessor join, including unrelated owners.
3. One-slot Linear loop header/rebound/join representation, exact
   absence of the spent predecessor, final closed loan, and duplicate
   live-header refusal under actual model transition premises.
4. Refusal of an apparently successful join whenever its represented
   source backedge retains an active loan.

These hold for **all related finite-model contexts**, not all native
Haskell executions. The exact source-cut relation remains an explicit
cross-language premise, independently checked on the scoped source
specimens in CI. There is no source-to-Core compiler correctness or
global implementation refinement claim.

## Admission and remaining obligations

The [CORR-3 preflight](../../.github/workflows/fsem01-corr3-finite-projection-preflight.yml)
checks GHC 9.6.7 strict production Haskell and real source replay,
and separately compiles all Rocq 9.2 predecessors and CORR-3, refusing
admitted/axiomatized claims, running compiled-object checks and printing
theorem assumptions.

Credit only after exact-head full checks, a fresh ready-for-review FSEM
claim guard, protected merge, and trusted release of the original
exclusive claim. General compiler/source-runtime correspondence,
arbitrary joins/loops, nested scopes and an executable extracted
reference interpreter remain open in FSEM-01/05/06.
