# Phase 1 storage allocation failure production binding v1

This slice closes machine implementation refinement for `PHIL-MEM-FAIL-001` / MEM-002--003 by binding the exact kernel staged in #670 to the production storage-realization checker.

## Exact kernel

The checked-in copies

- `generated/StorageAllocationFailureKernel.hs`, and
- `src/StorageAllocationFailureKernel.hs`

are byte-identical to the #670 Rocq extraction artifact. Their required SHA-256 is:

`7d1ba8b9667373d46b5756f8c709e5a18b8c052aae3d4ee35365ac5a3dc4019c`.

CI freshly recompiles `StorageAllocationFailure.v` and `StorageAllocationFailureImplementation.v`, re-extracts the kernel, verifies that hash, and byte-compares both checked-in copies.

## Production composition

`Phil.Systems.StorageAllocationFailureCertification` composes the existing production surface in this order:

1. `checkStorageRealizationCertified` runs first. This preserves unchanged `Phil.Systems.Storage` diagnostic ordering and requires the already implementation-refined `PHIL-MEM-REALIZE-001` seven-fact kernel.
2. The concrete allocation-failure disposition is independently reflected into the exact Certified MEM-002/MEM-003 case split.
3. The selected extracted disposition gate must accept.
4. The outer extracted `base realization valid && disposition valid` gate must accept, with the MEM-001 predecessor represented as one `True` fact only after step 1 succeeds.
5. Any native-success/kernel-reject disagreement fails closed and carries the reflected kernel facts.

Production `Phil.Systems.Storage` remains unchanged. The binding is a wrapper rather than a rewrite, so existing native errors and payloads retain precedence.

## Concrete reflection boundary

The proof model uses nonzero natural-number keys. The production reflection uses nonempty `Text` identifiers for the corresponding Haskell keys:

- mapped source failure identity;
- checked-capacity evidence identity;
- allocation-assumption identity; and
- deployment-requirement identity.

For mapped failures, the proof predicate `sourceFailureContains` is reflected by exact membership of the Haskell `StorageFailureKey` in `SourceStorageFailures`; `SourceStorageInfallible` reflects to false.

The six disposition families are bound exactly:

- physical allocation cannot fail: unconditional acceptance at this proof layer;
- maps to source: nonempty failure identity and exact declared-source membership;
- proved unreachable: nonempty capacity-evidence identity;
- assumption: nonempty assumption identity;
- deployment requirement: nonempty requirement identity;
- unaccounted: unconditional rejection.

## Retained boundaries

This implementation refinement does **not** prove the truth of capacity evidence, applicability of an assumption or deployment requirement, or concrete allocator/runtime behavior. OOM, abort, overcommit, retry, eviction, process-exit behavior, provider truth, target-profile facts, concrete `Text`/`Set` representation, diagnostics, Rocq extraction, GHC compilation, and runtime correctness remain explicit evidence/profile/TCB boundaries.

The general `PHIL-SYS-PARTIALITY-001` target UB/trap/capacity theorem remains separate. This binding only closes the bounded MEM-002/MEM-003 allocation-failure disposition relation already Certified by `StorageAllocationFailure.v`.

## Closeout criterion

A green exact-head merge requires:

- fresh extraction matching SHA-256 `7d1ba8b9667373d46b5756f8c709e5a18b8c052aae3d4ee35365ac5a3dc4019c`;
- byte identity of both checked-in kernel copies;
- strict Haskell typechecking;
- direct #670 extracted-kernel controls;
- implementation-refined MEM-001 predecessor production controls;
- production-binding controls, including native diagnostic precedence and fail-closed disagreement; and
- the unchanged 18-case MEM-001--006 corpus.

After that closeout, `PHIL-MEM-FAIL-001` may be promoted from **Certified** to **Implementation Refined**.
