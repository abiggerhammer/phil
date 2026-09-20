# R3 follow-up: exact LLVM block coverage

## Review and scope

This is the first implementation remediation slice for the 20 September 2026
follow-up review. Its base is `2b0e9982240b4b8d9a1a7a24cc4850be4cb5d331`.
The finding is in **Phil Phase 1 follow-up audit — 2026-09-20 — 4cf858f**,
R3 (P1), in the Phase 1 Code Reviews folder. The subsequent review at `2b0e998`
reports no production changes between those review pins.

The original R3 fix made the target function inventory exact. It did not make
each function's block inventory exact. A disconnected candidate block could
therefore have no runtime site or edge to check and still contribute ordinary
instructions. A scalar return in such a block could also alter the function
return type selected by the renderer's ascending block traversal.

## Implementation boundary

`verifyLLVMEmissionWith` now obtains each expected function's complete block
key set from the selected lowerer applied to the verified Systems artifact and
the verifier's target profile. It compares that set with the candidate before
checking per-block ordinary operations and terminators. Missing, additional,
or renamed keys produce `LLVMBlockSetMismatch`, with the function name and
both ordered key lists.

The candidate's own digest, retained edge witnesses, or surviving block list
cannot supply this expected inventory. Runtime coverage and edge checks remain
in place, but neither is treated as a substitute for whole-block coverage.

A selected lowerer may still explicitly supply helper functions and helper
blocks. This is not a blanket ban on disconnected code: the lowerer's exact
reference projection, rather than the candidate, must justify it. The
lowerer itself remains trusted at this API boundary; these tests do not
establish semantic correctness of an arbitrary caller-supplied lowerer.

The reference entry is also compared for every target function, including
helpers absent from the source function map. Existing ordered parameter and
exact terminator checks remain unchanged. In this IR there is no separately
stored return signature: the renderer derives it from return terminators.
Exact block keys plus exact terminators therefore pin the complete input to
that derivation to the independent reference projection. The tests check both
an added earlier return that changes the signature and later/same-width
additions that do not. They also retain rejection of a changed return width
inside an expected block. This is not a claim that all reference-generated LLVM
is well-typed; independent LLVM verification remains necessary, and R1's
concrete name-encoding defect is a separate open remediation.

## Regression evidence to collect

The existing `test/Phase1ReviewR3LLVMFunctionCoverageMain.hs` corpus now has 14
cases. It retains all three original function-coverage controls and adds:

- Disconnected return and ordinary-call blocks in a source-derived function.
- A valid U32 helper control, an earlier U64 return that changes its rendered
  signature, a later U64 return, and a same-width extra return.
- Positive reference-admitted helper blocks, plus deletion and equal-sized
  renaming of that inventory.
- Entry drift in an admitted helper and return-width drift in an expected block.

Every candidate mutation is re-rendered and has its target digest recomputed.
The block-inventory tests also check that function keys, entries, parameters,
runtime sites, control edges, and edge witnesses remain unchanged, and require
the specific block-set diagnostic rather than accepting an unrelated failure.

The permanent **Phase 1 Review R03 Function Coverage Proofs** workflow already
strict-typechecks and executes this test file with GHC 9.6.7 after building the
complete Haskell substrate. Changes to `src/Phil/LLVM/Verify.hs` also exercise
the existing R02 parameter-correspondence gate. No new staging workflow, Cabal
component, or redundant proof job is introduced here.

Status at authoring: implementation and regression code submitted for CI;
no local GHC/Rocq execution was available. Exact-head CI results and independent
review are required before closing R3. Existing R03 proof artifacts certify
their documented function-coverage boundary, not this newly added block-domain
check. This slice does not modify proofs, generated kernels, or assurance
ledger certification status, and it does not address R1, R10/R16, R13/R14-C1,
R17, or R18.
