# PHIL-P1-REVIEW-R02 proof boundary

This slice certifies Astra Review R02: independent Systems→LLVM validation must compare each function's complete ordered parameter list, including parameter identity and type.

The semantic rule is exact list equality against the independently selected lowerer's expected function:

- omission or insertion changes list length and rejects;
- name drift at any position rejects;
- type drift at any position rejects;
- reordering distinct parameters rejects; and
- the existing PHIL-LLVM-PRESERVE-001 conservative translation gate remains required.

The concrete Haskell authority is `verifyOrdinaryProjectionWith`, which reconstructs an expected LLVM module from the selected lowerer and compares `llvmFunctionParameters actualFunction == llvmFunctionParameters expectedFunction` before ordinary block projection checks.

The permanent R02 regression mutates a real BeginPolicyChoice lowering by omission, name drift, type drift, and first-two-parameter swap, while rebinding candidate text/digest so rejection is attributable specifically to parameter correspondence.

Concrete Text/LLVMParameterType representation, lowerer selection, Map traversal, target rendering, GHC/runtime correctness, and LLVM toolchain behavior remain explicit implementation boundaries.
