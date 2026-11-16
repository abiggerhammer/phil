# FSEM-01 CORR-4: executable finite Linear consume/insert correspondence

> **Non-normative, bounded proof and source conformance slice.** Parent [#1613](https://github.com/abiggerhammer/phil/issues/1613). Follows protected CORR-1 #1718, CORR-2 #1813 and [CORR-3 #1815](https://github.com/abiggerhammer/phil/pull/1815). This introduces no production checker, source grammar or normative semantic rule, and does not close FSEM-01 or Phase 1.

## What changes from CORR-3

CORR-3 related finite four-zone unrestricted/affine/linear/loan snapshots to extensional Rocq Core resource contexts, but its join/loop preservation theorems assumed successful Core transitions. CORR-4 supplies **computed, total finite decisions** for one Linear consume and one Linear insert.

The new [Rocq proof](../../proof/Phil/Surface/SurfaceFiniteLinearStepCorr4.v) defines finite-name deletion and executable finite consume/insert decisions. It proves, for every finite snapshot exactly related to an extensional Core context:

1. Name deletion has an exact lookup result for every possible query, not merely the selected owner or finite sample points.
2. A finite Linear consume either refuses an active loan, reports a missing Linear owner, or gives a typed successor whose four domains exactly match the corresponding Core consume transition. The outcome and relation are determined by the finite decision, not by a supplied success proposition.
3. A finite Linear insert refuses any name already present in U/A/L, or produces a successor whose entire four domains match a Core Linear insertion.
4. Borrowed-owner and duplicate-name checks take priority over a successful transition.

The theorem is universal **over the related Rocq finite/context model**, not over Haskell's Map/Set/Text runtime. Model UnknownLinearBinding is coarser than Haskell's additional WrongStructuralMode error. The native check verifies that distinction separately, without silently strengthening the Rocq theorem.

## Native checked-source evidence

The [strict native driver](../../test/Phase1FSEM01Corr4LinearStepMain.hs) reparses and checks six original Grammar-v1 Linear loop fixtures: accepted owner transfer, same-width spectator, stale original owner, duplicate live header, unproved invariant and accepted closed scoped loan. It observes authentic source-produced entry/consume, header insertion, continuing-actual consumption, backedge reinsertion and refusal cuts, then independently replays each reached Core consume/insert result with a finite-list decision engine.

The finite projection checker compares every owner in both the native and finite domains and additional absent-name probes across U/A/L/active loans; it refuses cross-zone or within-zone duplicates. It checks exact native error constructors for borrowed owner, absent owner, wrong mode in U/A and duplicate in every mode. Forged controls include extra/omitted Linear owners, wrong structural mode and checked type, fabricated loan, duplicate keys, tampered entry-consumed state and tampered header state.

An unproved source invariant stops *before* the backedge resource transition. This slice does not invent a Core step for it merely to make the model total.

## Assumptions and unclosed boundaries

- Source-checker state versus Rocq Context and finite snapshot: **bounded native conformance tests only**. The Rocq proof assumes an exact finite relation and cannot by itself establish it for arbitrary Haskell states.
- Context native implementation, Haskell Map/Set/Text behavior, source parser and declaration identity, error-precedence correspondence for other language constructs, actual runtime loop iteration and Source→Systems realization all remain separate.
- This is one Linear owner move/reinsert, not arbitrary mixed-mode/affine ownership, dependent/multi-slot loops, general source operational semantics or an extracted interpreter. FSEM-05/06/07 and PHIL-ASSURE-IMPL-CORR-001 remain open.

CI for this slice requires strict GHC 9.6.7 warning-free tests, Rocq 9.2.0 compiled predecessor and current modules, no Admitted/Axiom/Parameter, named Print Assumptions, recursive compiled proof check, full PR exact-head checks, fresh post-ready FSEM claim guard, and normal protected merge and trusted claim release. A passing conformance test does not claim native equivalence by itself.
