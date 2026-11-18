# P9-G3 R1b/R2 — closed SteveGet proof-only preflight

**Status:** CANDIDATE MODEL THEOREMS ONLY. Not a Phil source operational-semantics proof, not a checked translation/refinement of the real manually supplied Core, not a linked-ABI/native proof, and not release/TCB authority. This scratch branch must not be merged as an F2 implementation or used to mint conditional evidence.

## Pin and unchanged authority boundaries

- Frozen P9 scratch ancestor `302c61877991f38dae2f64cd4a29eadfb2757046` (`p9-preflight/f2-g3-20261118`), containing the actual original-raw-source structural checker, native witness and the already-tested source/System/ABI gate. The new branch only adds this document, the new proof file, and an unprivileged preflight workflow. It does not modify those prior nine P9 paths, main, FSEM-05/06, or the P9 implementation worker.
- [Original source](../../examples/steve/get.phil); [selected manually authored Core](../../src/Phil/Examples/Phase1/SystemsWitnesses.hs) (`steveGetFunction`); [real static source/Core discriminator](../../src/Phil/Compiler/SourceCorePolicy.hs) (`verifySteveGetStructural`); [real source producer](../../src/Phil/Compiler/SourceSystems.hs) (`produceVerifiedSourceSystems`); [modeled ABI checker](../../src/Phil/Assurance/P9SteveGetCorrespondence.hs).
- Parent [P9-F2 #1805](https://github.com/abiggerhammer/phil/issues/1805), [R1/R2 independent review #1851](https://github.com/abiggerhammer/phil/issues/1851), [FSEM-05/06 #1613](https://github.com/abiggerhammer/phil/issues/1613), independent native [#1826](https://github.com/abiggerhammer/phil/issues/1826).

## Exact mathematical result

`proof/Phil/Verification/P9G3SteveGetClosedRefinement.v` defines a **new proposed semantics**, not an imported established Phil execution relation:

1. `P9SourceState` and `p9_source_step` model one `SteveGet` invocation with `read.found`, a fresh abstract owner tagged by invocation+found serial, a unique live lexical borrowed view, one digest result, loan close before branch release, and two no-owner return alternatives.
2. `p9_r1b_model_reachable_scoped`: all reachable candidate source states preserve the exact owner and loan-incarnation association. `p9_r1b_model_digest_live_original_loan`: an actual model digest step can only originate in the `P9SBorrow` state, with a loan belonging to the original selected read owner. `p9_r1b_model_strict_step_rank`: every model step advances strictly, precluding a second digest/read within this model invocation.
3. `P9CoreState` and `p9_core_step` model the exact *shape* of selected Core `get.entry/get.check/get.ok/get.integrity-failure` but are not actual Haskell Core runtime transitions.
4. `p9_r2_model_source_to_core_weak_step`: all candidate source steps project to exactly one candidate Core step or a stutter; **loan open and close are the stutters**. `p9_r2_model_core_reachable_scoped` + `p9_r2_model_target_digest_original_invocation` provide a *target-side* reachability/safety property, not just an existential forward simulation. This matters: a forward simulation alone does not exclude extra target traces.
5. `p9_r2_model_distinct_owners_even_equal_bytes`: different dynamic invocation identities imply distinct owners regardless of payload, hash, capability root or native pointer equality. This is a ghost-world statement, **not** a real C ABI freshness or ABA check.

`P9Pin` retains invocation, ContentId operand and selected nominal K/I values in both mathematical machines. The hosted native regression checks the **real parsed and checked source and actual selected Core** separately; it does not imply the Rocq step relation is an adequate model of either real evaluator.

## Exact outstanding proof/authority links

- **R1b actual semantics adequacy, unproved:** Derive the candidate transition rules from Phil's real accepted execution judgments for `DecideExpression`, `BorrowExpression`, primitive outcome and release semantics. The current `SourceCheckedProviderFound`/`SourceCheckedLoanOpened`/`SourceCheckedLoanClosed` events are **static checker observations**, not a dynamic trace. FSEM-05's source-wide executable interpreter/operational semantics are not silently supplied by this file. If no accepted semantics exist for this fragment, request the narrow FSEM-05 semantic review; do not assert the simulation as normative.
- **R2 selected-Core adequacy, unproved:** Prove `steveGetFunction` actual Core state-transition semantics and result/value/CFG behavior refine `p9_core_step`, with caller-supplied Core not treated as a compiler-derived proof. An independent validator must select the exact raw source unit/declaration/K/I/branch/span and exact Core `get.id`/`get.bytes-view` operands, read-found predecessor and release successor; the present Haskell checker is structural only.
- **R3/R4**, still unproved: LLVM/ABI generation, independently selected linked object/revision, native allocation and pointer-/loan-generation refinement. A/B valid-pair replacement is accepted by the raw native FFI under current API; a ghost relation does not make it reject. The compiled app does a second host read/check and ignores the first native return.
- **G4**, forbidden now: no conditional `DigestMatches` minted, no actual source proof-use, no E3/P7 use, no weakening of F1 `KernelChecked`, no new trusted SHA/Blob rule or new TCB assumption. F2 and E3 each remain **0/1 spent**; original P9 hourly worker remains disabled.

## Hosted proof evidence required

Workflow `.github/workflows/p9-g3-r1r2-proof-preflight.yml` is scratch-only, contents-read, no protected write or release privilege. It compiles the new proof using Rocq 9.2.0, prints all seven named theorem assumptions, rejects `Axiom/Parameter/Admitted/admit/Abort`, invokes `rocq check` for the compiled object, and prints source/object/assumption hashes. A separate warning-free GHC 9.6.7 job runs the **existing actual** `Phase1INT001WitnessE2EMain.hs` static source/selected-Core discriminator and existing negative tests. Neither separate green result proves a Haskell↔Rocq semantics correspondence.

After hosted results: post exact branch commit/CI outcomes and first unresolved adequacy lemma to #1851 and #1805. Do **not** open the F2 PR or reactivate its worker without an independently justified real-language theorem and its required implementation/ABI evidence.
