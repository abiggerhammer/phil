# P9-G3 / FSEM-05–06 — selected SteveGet executable-fragment adequacy preflight

> **Non-normative, proof-only preflight.** The result is a candidate executable source semantics plus exact whole-AST/whole-Core discrimination of the **actual selected** SteveGet. Neither a successful Rocq proof about the proposed semantics nor an independent Haskell shape check establishes that Phil's actual source program executes those semantics. No new trusted premise, F2 merge, P7 proof mint, Phase-1 freeze or release authority is created.

## What is being tested

Predecessor: verified [R1/R2 proof-only run #44336186371](https://github.com/abiggerhammer/phil/actions/runs/44336186371), head `f5a84e875afba18f96e7b62465c6134295feb3c5`; source P9 G3 scratch `302c61877991f38dae2f64cd4a29eadfb2757046`. This is a **new disjoint scratch branch**, not a modification of either predecessor branch or a formal-semantics family claim. FSEM-02 #1897 and its exclusive claim are untouched.

### FSEM-05 candidate *fragment*, not actual-language adequacy

`proof/Phil/Verification/P9G3SteveGetExecutableFragment.v` imports the preceding verified **candidate** `P9SourceState` and `p9_source_step`, and defines:

- `p9_source_next`, a computable transition function for exactly the closed read→found→borrow→digest→loan-close→release path plus the no-owner not-found and storage-failure paths.
- Explicit environmental choices: read-found serial, read outcome, chosen digest outcome, claimed content, claimed owner and claimed loan. The last two are **proof-ghost inputs not present in the current native ABI**.
- `p9_fsem05_fragment_step_sound`: every successful executable source step is a step of the prior *candidate* declarative relation.
- `p9_fsem05_fragment_step_complete`: every candidate declarative step has a matching explicit executable choice. Not a theorem about the Haskell Surface checker.
- `p9_replay`: fuel-bounded deterministic replay distinguishes **normal completion**, **invalid choice**, **missing input** and **out of fuel**. Digest rejection gives the distinct normal `P9IntegrityFailure` outcome; external-choice rejection must not be confused with production semantics or normative rejection.
- Positive examples for accepted digest, rejected digest, missing blob and storage failure; negative examples for cross-invocation substitution, stale (ABA-like) *ghost incarnation*, wrong content operand and digest before borrow.

Rocq `Print Assumptions`, no admitted hypotheses, compiled object `rocq check` and SHA receipts must be verified on the current exact head. No claim of an independently extracted interpreter, full Phase-1 execution coverage, or actual provider operation law is made.

### FSEM-06 selected source/Core *syntax* pin

`test/P9G3SteveGetSelectedShapeMain.hs` runs the **existing production parser** on the **actual** `examples/steve/get.phil`, rechecks the **entire AST spine**, and compares the independently handwritten exact expected CFG and role map against the existing **manually authored** `steveGetFunction`. It rejects:
- source found-binder change, wrong borrowed owner, swapped digest operands, duplicate digest call, renamed result binder, wrong release owner and altered not-found branch;
- Core reordered digest operands, omitted release, early release, changed entry, and extra unreachable block.

This complements, but does not replace, the existing private `produceVerifiedSteveGetCanonicalSource` / `verifySteveGetStructural` and strict source/Core real-integration tests. AST/CFG equality is stronger than matching operation names somewhere, but still says **nothing about execution effects or compiler correctness**.

The old proof `p9_r2_model_source_to_core_weak_step` is reused to prove the new executable model's weak step projection; source loan-open and loan-close stutter because Core does not represent them. Independent target-model reachability safety is retained so the forward simulation isn't misread as exclusion of extra target traces.

## The precise *still-missing* semantics that block R1b/R2 real adequacy

1. **FSEM-05 actual source execution judgment**: there is no identified independently adopted, executable source small-step interpretation for the exact selected `DecideExpression (blob_read...)`, `found(bytes)`, lexical `BorrowExpression`, real outcome-qualified `digest_check`, loan close, release and `return unit`. The existing `Surface.Check.Engine.evalBorrowTraced` is **checker trace** data from `checkScopedValueBlock`, not a provider runtime machine; a `SourceCheckedLoanOpened` observation is static, not fresh dynamic owner identity. The small-step semantics needs explicit real `BlobProvider.read.found` allocation freshness, content ID preservation, typed decision outcome, live loan generation, and release finality. It must specify what happens when the real provider errors, blocks, or produces another result occurrence.
2. **FSEM-06 actual source→manual-Core validator soundness**: (R1b) would need to be combined with a real execution rule for the exact `get.entry/get.check` supplied Core, including dynamic handling of the `get.bytes` object and `CoreBorrowedValue get.bytes`. The present exact syntactic discriminator does **not** prove a correct target trace (including no extra target behaviors) follows from accepted source observations; the old `SourceCore.verifyFunction` checks terminal/inventory coverage, not operational simulation. Prove a source and Core *adequacy lemma* about real transition rules rather than assuming the new model describes Haskell/GHC.
3. **R3/R4 ABI/link boundary remains separate**: the selected LLVM erases `BorrowedSlice` to an owner pointer. Native `steveDigestCheck` checks a pair selected by the **supplied** content handle; switching both handles to another valid same-content B read is accepted at the raw API. Recycled StablePtr bits may cause ABA. The Rocq ghost serial and source-specific AST check do not authenticate runtime identity or prove the selected linked build matches the original source. Independent #1826 build attestation and linked machine refinement are not provided by this slice.
4. **G4 is not authorized**: `get.phil` has no original `TyProof` consumer. The host launcher ignores compiled SteveGet's return and does a second read/check for publication. No accepted-only conditional `DigestMatches` can be minted from these tests; `assumption:sha256-semantic-profile.v1` and actual Blob provider assumptions remain **UNDISCHARGED**. F1's assumption-free `KernelChecked` remains unchanged.

### Requested separate semantic decision

If qualified FSEM-05/06 maintainers find the narrow above execution rules absent, the **smallest missing authority** is a reviewed closed-`SteveGet` operational fragment with explicit read-found owner-incarnation and loan-generation transitions, plus a separately checked sound translation validation to the selected manual Core and no-extra-target-traces property. This is a *proposal* for independent semantic review, **not** a new axiom, a blanket FFI rule, a runtime generation token, or permission to modify FSEM-05/06 files. If that cannot be established without expanding accepted TCB, stop and make the new trust decision explicit.

**Gate:** even if focused tests and object checks pass, hold P9-G3 STOP, no P9-F2 official PR, no P9 worker restart and no E3/P7/Phase-1 closeout claim. The prior P9 scratch remains untouched, F2/E3 0/1 PR slots unused.
