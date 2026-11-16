# FSEM-01 CORR-7 / J-4 — terminal-aware predecessor joins

> Non-normative, bounded evidence slice following protected [CORR-6 #1820](https://github.com/abiggerhammer/phil/pull/1820). Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613). No normative source grammar, production checker, approved TCB, or release authority changes.

## The distinction CORR-7 must preserve

The lower-level Core joinContinuing on an empty list returns an empty resource context. That must **not** be treated as a reachable continuation when a source branch has **all terminal predecessors**. The production Surface checker already excludes terminal paths and refuses further source control after both arms terminate. The new finite Rocq model represents continuing, terminal, and failed predecessor observations separately, and computes NoContinuation, Joined, JoinRejected, or SourceRejected.

## Arbitrary-finite model and priority

The [Rocq finite model](../../proof/Phil/Surface/SurfaceFiniteTerminalJoinCorr7.v) checks all loan sets **before any** unrestricted/linear comparisons, checks all Unrestricted contexts against the first continuing predecessor, then all Linear contexts, and finally folds Affine intersections left-to-right. Earlier Affine removal cannot be undone by a later predecessor. A source failure takes precedence over a resource join, without fabricating a successor. The module proves all-terminal exclusion, sticky source failure, one loan-free survivor preservation, loan/U/Linear priority, exact successful Γ/Δ/loan fields, and arbitrary-finite Affine owner non-resurrection.

CORR-6's two-continuing-predecessor soundness theorem remains the extensional Core-model foundation. This slice does not claim a universal Haskell map/set/type equality refinement: general Syntax.Ty equality and accepted native Text/Map/Set correspondence remain separate obligations.

## Real source and independent native evidence

The [strict GHC 9.6.7 test](../../test/Phase1FSEM01Corr7PredecessorsMain.hs) uses the existing production Grammar-v1 source checker on **six actual if/join source programs**:

| Checked source fixture | Classified predecessors | Source result |
| --- | --- | --- |
| accepted | continuing / continuing | accepted joined Linear return |
| linear-mismatch | continuing / continuing | exact incompatible Linear join refusal |
| two-local-owners | continuing / continuing | distinct sibling-owner Linear refusal |
| terminal-excluded | terminal / continuing | surviving predecessor, accepted |
| terminal-stale | terminal / continuing | valid join followed by stale structural use refusal |
| terminal-both | terminal / terminal | no continuing successor; ControlAfterTerminal |

An independent sorted-association-list finite oracle also checks three, seven, and fifteen Core predecessor states, global loan-before-U, U-before-Linear, Linear-before-Affine, and Affine first-branch non-resurrection. Its predicted result is compared with production Core.joinContinuing; it does not manufacture its prediction by calling that implementation.

The model can represent a pre-join source failure, but these six original-source transcripts cover terminal, join and post-join failure paths, **not every pre-join source-error classification**. Bounded adapter noncompetence is never asserted to make source invalid.

## Original-source artifact and independent replay

The native driver emits six canonical versioned source records with source SHA-256, declaration root, real checked flag/payload Core identities, selected predecessor categories and observed source result. The [independent validator](../../scripts/fsem01_corr7_source_predecessor_witness.py) checks exact original source bytes, declaration and binder ordinals, canonical length-framing, the full six-file corpus and hostile version, digest, role, predecessor and result mutations.

The [Rocq wire decoder](../../proof/Phil/Surface/SurfaceSourcePredecessorWireCorr7.v) proves decoding integrity and independently computes a bounded finite model result for the checked source profiles. A dependent CI job compiles literal Rocq witnesses constructed from the **same Haskell-emitted source bytes**. The decoder's fixed common source type is not a general proof of native Ty equality; Rocq does not independently rehash the source files, and the Python validator does not prove the Haskell producer universally faithful.

## Merge and scope boundaries

Require focused Rocq 9.2.0 compilation, named Print Assumptions, recursive object checking, strict GHC -Wall -Werror, independent SHA/negative validation and actual literal replay; then **all** exact-head PR checks, a fresh post-ready two-job FSEM claim guard, protected squash with expected head and independently trusted claim release.

Still open: FSEM-01 general R10/R11/R15 coverage, restricted/dependent join telescopes (JOIN-05), arbitrary match, nested borrowing and loops, source-to-Rocq refinement, FSEM-05/06/07, P8/P9/P10, and Phase 1 freeze. FSEM-02 ownership remains separate.
