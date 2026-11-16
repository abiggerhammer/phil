# FSEM-01 CORR-6 / J-3 — executable finite mixed-resource branch join

> **Non-normative, bounded evidence slice.** Follows protected CORR-5 [#1819](https://github.com/abiggerhammer/phil/pull/1819); tracked in [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613). Does not alter production checker semantics, promote a source adapter's noncompetence into invalidity, or close FSEM-01/05/06.

## Selected existing source competence

The [real source adapter](../../src/Phil/Surface/GrammarV1/SourceAffineIfJoinResource.hs) parses Grammar-v1 declarations and performs actual nominal Affine Permit admission, type/mode/lineage checks, lexical branch resolution, production scope pruning and `Core.Context.joinContinuing` before checking the post-join source continuation. A nominal Permit's Affine mode depends on an **externally admitted lifecycle attestation**; source spelling is not sufficient authority.

The new [strict independent native driver](../../test/Phase1FSEM01Corr6MixedJoinMain.hs) re-runs six existing authentic source cases: asymmetric Affine disposal, retained Affine owner on both sides, two sibling same-spelling branch locals with distinct semantic identities, an Unrestricted branch-local declaration pruned before joining, a live Linear local that fails scope cleanup **before any join**, and an Affine permit stale use that fails **after a valid join**. It checks exact Γ/A/Δ/loan maps and branches against a new finite **list-based**, independently computed mixed join, rather than using production Map.intersection to construct its answer.

Adversarial controls reject active left or right loans, unexpected Unrestricted/Linear map disagreements, conflicting Affine owner types, duplicates across zones, malformed loan ownership and fabricated joined Affine successors. The first-order refusal order is native: active loan first, U mismatch, Linear mismatch, Affine intersection/type mismatch. The Affine check intentionally visits the **first** continuing predecessor's active bindings; an owner dropped there cannot be resurrected or trigger a late error from a second-branch mismatch.

## Rocq model and exact boundary

[SurfaceFiniteMixedJoinCorr6.v](../../proof/Phil/Surface/SurfaceFiniteMixedJoinCorr6.v) computes total finite join decisions across Γ/A/Δ/loans. The type equality oracle is **a parameter to the function**, with a required *sound and complete equality reflection law* for model correspondence. That law is not silently assumed as part of Haskell's `Eq Ty`, nor is generic Unicode Text/Rocq String equality discharged by checking source fixtures.

Its proof obligations include universal lookup-based U/Linear equality equivalence, exact possible Affine retention, model-joined output and rejection/no invented successor. Its result is limited to **two continuing predecessors**; terminal, rejected or failed-source predecessors are not equivalent to a successful continuing branch. The native driver uses the previously accepted source path and treats the live Linear branch-local failure as a **pre-join** rejection, not a Core join failure.

The model proof and native source evidence must pass strict Rocq 9.2 and GHC 9.6.7 -Wall -Werror CI with a full exact-head PR census, a fresh post-ready claim guard, protected expected-head squash merge and independently trusted exact unique-claim release. The general source↔Haskell Map/Set/Text↔Rocq refinement remains a separate, open obligation. This slice improves R10/R11/R15, but does not cover arbitrary source match, nested/dependent join telescopes, unbounded control flow or FSEM-05's full extracted interpreter.
