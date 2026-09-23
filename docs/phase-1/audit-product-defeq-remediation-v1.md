# PHIL-AUD-PRODUCT-DEFEQ-001 — product definitional equality remediation

## Finding

The Phase 1 implementation audit found that `Phil.Core.Value.equalTy` had no `TyProduct` case. Consequently even an identical `TyProduct` compared definitionally unequal, and exposed `checkValue` could reject a product binding against the exact type that `Phil.Core.DataMode.formProductBinding` had just installed.

This is the implementation-side completeness/correctness finding `PHIL-AUD-PRODUCT-DEFEQ-001`.

## Repair

`equalTy` now compares product types structurally under its current binder environment. Product equality requires:

- exact element arity;
- exact element order;
- exact structural mode for every element; and
- recursive definitional equality of every element type using the same binder environment.

The repair deliberately does not use a reflexivity shortcut. Recursive element comparison preserves alpha-equivalence for dependent types nested inside products, including endpoint payloads whose binders are renamed.

## Permanent replay

`test/Phase1AuditProductDefeqMain.hs` records the audit obligations as permanent regressions:

- P01 empty-product reflexivity;
- P02 unrestricted Bool-product reflexivity;
- P03 linear exact-Bytes product reflexivity;
- P04 nested-product recursion;
- P05 alpha-renamed dependent endpoint elements;
- P06 arity mismatch rejection;
- P07 element-mode mismatch rejection;
- P08 element-type mismatch rejection;
- P09 order sensitivity;
- P10 the public `compareTypes` equality boundary; and
- G01–G03 producer-to-consumer checks beginning at the genuine `formProductBinding` path, including unrestricted, linear-Bytes, and nested products.

The dedicated workflow also reruns DATA-015 finite-product ownership controls and the existing alpha-shadow regression suite.

## Assurance boundary

This closes only concrete Haskell `TyProduct` definitional equality and the exposed producer-to-value-checker consumer path. It does not add new product syntax, change formation/elimination ownership rules, establish a new Rocq correspondence theorem, or alter native/LLVM lowering. Existing product proofs and extracted kernels retain their previously stated representation/correspondence boundaries.
