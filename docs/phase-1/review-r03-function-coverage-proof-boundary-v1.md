# PHIL-P1-REVIEW-R03 proof boundary

This slice certifies Astra Review R03: independent Systems→LLVM validation is closed-world over the complete function inventory emitted by the independently selected lowerer.

The semantic rule is exact function-inventory equality between the selected lowerer's expected module and the candidate module:

- every expected function must be present;
- every candidate function must be expected;
- an unadvertised target-only helper rejects;
- omission of an expected function rejects; and
- a helper is admissible only when the selected lowerer itself emits it, so it becomes part of the expected inventory rather than a verifier exception.

The aggregate proof composes that exact inventory rule with the existing PHIL-LLVM-PRESERVE-001 conservative translation gate.

The concrete Haskell authority is `verifyOrdinaryProjectionWith`. It reconstructs the expected LLVM module with the selected lowerer, compares `Map.keys actualFunctions == Map.keys expectedFunctions`, and raises `LLVMFunctionSetMismatch` before entering per-function parameter/block correspondence.

The permanent R03 regression exercises a real Storage lowering in three cases: the unchanged module passes, a target-only helper inserted after lowering rejects, and the same helper passes when an explicitly selected lowerer emits it.

Concrete Text identity, Map key ordering, lowerer selection/execution, target rendering/digest rebinding, GHC/runtime correctness, and LLVM toolchain behavior remain explicit implementation boundaries.
