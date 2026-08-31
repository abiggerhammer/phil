# Data identity production binding v1

This closes the bounded implementation correspondence for Certified `PHIL-DATA-ID-001` staged in #459.

## Exact extracted kernel

The Rocq-extracted `DataIdentityKernel.hs` is checked into `src/` byte-for-byte from the successful #459 staging run.

Expected SHA-256:

`237c3232c586627f5b79b77657deb035f9480e73bb474950c202e2e763ec609c`

The production-binding workflow fresh-extracts the kernel with Rocq 9.2.0, requires byte identity with the checked-in file, and asserts this exact digest before any production correspondence check may succeed.

## Production binding

`Phil.Core.DataIdentity` retains recursive transparent-alias traversal and concrete nominal-key equality as native Haskell representation facts. The final equality fact is passed to `decideDataIdentityByFact`; the returned extracted constructor alone selects the public Boolean result.

`Phil.Core.DataOperationContract` retains the concrete `DataOperation` constructors, `Data.Set` storage, insertion, membership, and canonicalization as native Haskell representation facts. Exact membership of the requested operation is passed to `decideDataOperationByFact`; the returned extracted constructor alone selects the public Boolean result.

The operation path never receives identity or shape as an authority input. This preserves the Certified non-inference boundary: nominal/definitional identity cannot manufacture equality, hashing, cloning, serialization, ABI compatibility, memcpy safety, or any other operation grant.

## Explicit native / predecessor boundary

The following remain outside the extracted kernel:

- recursive `TransparentAlias String DataTypeRef` traversal;
- concrete nominal-key / `String` equality;
- source declaration-key, checked-shape, and alias elaboration correspondence;
- concrete `DataOperation` constructor correspondence;
- `Data.Set` insertion, membership, and canonicalization;
- truth and competence of explicit provider/prelude operation contracts;
- diagnostics and source presentation;
- GHC/Haskell runtime correctness; and
- Rocq extraction/toolchain correctness.

## Closeout criterion

A green exact-head production-binding run must:

1. recompile the Certified theorem and executable correspondence;
2. fresh-extract `DataIdentityKernel.hs`;
3. byte-compare it with `src/DataIdentityKernel.hs` and assert the harvested SHA-256;
4. strict-typecheck the fresh and checked-in kernels;
5. execute the direct decision controls against the checked-in production kernel;
6. strict-typecheck the bound `DataIdentity` and `DataOperationContract` paths; and
7. rerun the unchanged DATA-010 and DATA-011 pressure corpora.

After that exact-head matrix is green, `PHIL-DATA-ID-001` may be promoted to `Discharged / Implementation Refined`.
