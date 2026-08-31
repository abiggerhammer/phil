# PHIL-PROT-MSG-001 production binding v1

This closes the bounded implementation-refinement correspondence for the already-Certified protocol Message admissibility obligation.

## Exact extracted kernel

Production checks in `src/ProtocolMessageAdmissibilityKernel.hs`, byte-for-byte from the successful #452 extraction.

SHA-256:

`654d5ffb09fdb6ad2adddbd99e608ddbd39ef5e260c2b40beea63216f423a984`

The production workflow fresh-extracts the kernel from Rocq, byte-compares it to the checked-in file, and asserts this hash before running Haskell correspondence checks.

## Bound production choices

`src/Phil/Core/Protocol/MessageAdmissibility.hs` reflects five native facts into `decideBoundaryMessageContractByFacts` in the existing production precedence:

1. contract revision is nonempty;
2. contract type exactly equals the actual Core type;
3. contract semantic form exactly equals the actual semantic form;
4. native recursive semantic-shape traversal finds no forbidden constituent; and
5. native recursive hard-type traversal finds no forbidden Core type.

The extracted decision selects the same public diagnostic class. Native traversal still supplies exact aggregate/product paths and detailed inadmissibility values. Accepted contracts return only when the extracted kernel accepts all five reflected facts.

Bare concrete session-message admission keeps native recursive type traversal as the reflected fact and routes the final yes/no choice through `decideIntrinsicBoundaryMessageByFact`.

## Preserved native/predecessor boundaries

This closeout does not move these responsibilities into the extracted kernel:

- concrete Haskell `Ty`, `SemanticForm`, and `Text` representation/equality;
- recursive aggregate/product/refinement traversal;
- exact diagnostic path and detail construction;
- generic protocol-family instantiation and session substitution;
- boundary-message semantic classification that supplies the contract shape;
- resource ownership transfer and concurrency semantics;
- any future remote endpoint/channel passing or distributed capability delegation;
- GHC, Rocq extraction, runtime, target serialization, ABI, and wire correctness.

The two private fail-closed bridge sentinels in production are unreachable under the byte-checked kernel because `shapeAllows`/`hardTypeAllows` are derived directly from the cached native diagnostics. They exist only to keep the Haskell match total if a corrupted or noncorresponding kernel were substituted.

## Closeout criterion

`PHIL-PROT-MSG-001` may move from **Discharged / Certified** to **Discharged / Implementation Refined** only after an exact-head run:

- recompiles the Certified theorem and implementation correspondence;
- fresh-extracts the kernel and byte-compares it to production;
- asserts the harvested kernel SHA-256;
- strict-typechecks the checked-in kernel and bound production paths;
- executes direct extracted-kernel controls against the production kernel; and
- reruns the unchanged Message-admission, projection, and restricted-transfer pressure corpora.
