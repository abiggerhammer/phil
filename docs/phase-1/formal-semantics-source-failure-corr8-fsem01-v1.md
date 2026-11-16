# FSEM-01 CORR-8 — original-source pre-join failure-prefix correspondence

**Proposed, non-normative, bounded evidence.** Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613), exit R05/R11/R15 and [CORR-7](formal-semantics-terminal-predecessors-corr7-fsem01-v1.md). This work does not edit the production checker, P9's selected Steve provider evidence path, source grammar, TCB, or compiler/runtime ABI.

## The missing predecessor distinction

CORR-7 distinguishes a source rejection from a Core join rejection, a normal joined resource context, and a branch collection with no continuing predecessor. Its six real source tests cover terminal paths and ordinary join failures, but leave source errors *before* the ordinary join outside the original-source replay.

CORR-8 uses existing production traces and independently checked Grammar-v1 originals. The strict [Haskell witness driver](../../test/Phase1FSEM01Corr8SourceFailureMain.hs) checks the ordinary checker and tracing checker agree, verifies the source-rooted flag/owner identities and original resource context, and observes how far each source branch actually advanced. It refuses any invented post-error joined state.

| Source specimen | Left / right loan phases | Reached pruned predecessors | Actual classification |
| --- | --- | --- | --- |
| accepted-left.phil | B-S-V-C / none | 1 / 1 | completed Linear return |
| accepted-both.phil | B-S-V-C / B-S-V-C | 1 / 1 | completed Linear return |
| escape-left.phil | B-S-E-X / none | 0 / 0 | BorrowEscape; sibling unprocessed |
| escape-right.phil | none / B-S-E-X | 1 / 0 | BorrowEscape; earlier arm does not imply a join |
| escape-alias.phil | B-S-E-X / none | 0 / 0 | BorrowEscape through borrowed view alias |
| move-while-loaned.phil | B-S / none | 0 / 0 | StructuralUse, failed move |
| return-inside-borrow.phil | B-S / none | 0 / 0 | LinearCompletion, no successful loan closure |
| borrow-unrestricted.phil | B / none | 0 / 0 | BorrowEscape, no loan started |

B = BeforeLoan, S = LoanStarted, V = BodyResult without escaping view, E = BodyResult containing escaping view, X = EscapeRejected, C = LoanClosed, R = OwnerReturned. The exact original-source return-in-borrow prefix must be confirmed in CI; the proof never invents a loan-close transition.

The source-only error happens **before** a native Core join and differs from the resource-join mismatch established by CORR-7. An out-of-adapter source remains *noncompetence*, not a normative invalid-program verdict.

## Independent source bytes and model correspondence

The driver emits one PHIL-FSEM01-CORR8-V1 record for each of eight original source fixtures. Each record contains ten canonical ASCII length-framed fields: source SHA-256, exact declaration root, exact source flag and owner binder identities, profile, two actual loan phase prefixes, two counts of successful pruned predecessors and the original result class.

[The independent validator](../../scripts/fsem01_corr8_source_failure_witness.py) rereads original source bytes, checks digest, UTF-8 root/ordinal identities, exact prefix/branch/failure classification and canonical framing. It exercises hostile mutations including swapped owners, incorrect source digest, false loan closure, fabricated successor and forged success, then generates a Rocq witness using the literal original Haskell-produced wire.

[Rocq model theorems](../../proof/Phil/Surface/SurfaceSourceFailureCorr8.v) reuse CORR-7's finite replay. After any failure-free finite prefix, the first failed source predecessor produces SourceRejected and **cannot** yield Joined. They distinguish left-arm failure (no legitimate sibling processing) and right-arm failure (a previously valid predecessor cannot authorize a join). [The strict decoder](../../proof/Phil/Surface/SurfaceSourceFailureWireCorr8.v) validates all ten fields, compares exact expected source profile with an independently computed finite replay result, and rejects forged model outcomes.

## Exit gates and trust boundary

Focused CI must complete strict GHC 9.6.7 -Wall -Werror native source tests, existing borrow and CORR-7 regressions, independent hostile-witness validation, Rocq 9.2 compiled proofs and the generated exact-byte witness replay. Full PR exact-head checks, fresh post-ready claim guard, protected expected-HEAD squash and verified claim release are separate final gates.

This is bounded **source observation to finite replay correspondence**, not universal Haskell Map/Set/Text-to-Rocq refinement, general source failure simulation, a runnable Phase-1 interpreter, whole-language semantics, or FSEM-01 closure. Nested loans, arbitrary match/decide, dependent and multi-slot joins, runtime traces, FSEM-05/06 and assurance remain open. P9-F2's Engine, support, provider, verification and ABI sites are not touched.
