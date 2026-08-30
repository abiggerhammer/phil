# Boundary progression implementation refinement v1

`PHIL-BND-PROGRESS-001` is already Certified. This staging slice adds an executable, representation-neutral correspondence layer without changing production.

## Certified decision surface

The extracted kernel owns three bounded semantic decisions:

1. receive progression, in order: exact grammar correspondence, exact source-value correspondence, then the underlying receive progression result;
2. complete-emission disposition over the Certified four-way enum: invalid extent, partial emission, complete emission, or past-declared-frame emission; and
3. send progression, in order: exact representation correspondence, exact output-owner correspondence, then the underlying send progression result.

Successful complete emission also constructs an exact two-coordinate plan carrying the generated representation and output owner unchanged.

## Native bridge boundary

Production continues to own concrete Haskell `Int` arithmetic and therefore the reflection from intended/emitted byte counts into the Certified emission-disposition enum. Negative/overflow behavior, byte-count observation, transport-completion truth, actual wire I/O, and provider/target transport semantics remain explicit native or separate boundaries.

Likewise, concrete `Name` / `BoundaryRepresentationId` equality and the truth of predecessor `ParsedWitness`, `CorrespondenceEvidence`, and `GeneratedEncodingEvidence` objects remain outside this kernel. The kernel does not re-prove predecessor obligations.

Underlying `commitReceive` and `sendEndpoint` execution remains native. The extracted layer owns only whether exact reflected identity facts plus the reflected underlying result permit semantic progression.

## Staging verification

The registered `Phase 1 Boundary Progression Proofs` workflow is extended additively to:

- compile the Certified proof and implementation-correspondence proof;
- fresh-extract `BoundaryProgressionKernel.hs`;
- strict-typecheck the extracted kernel under `-Wall -Werror`;
- run 13 direct controls covering receive precedence, all emission dispositions, exact completion-plan construction, and send precedence;
- strict-typecheck unchanged production and the unchanged BND-011 test harness;
- rerun the unchanged four-case BND-011 progression corpus; and
- record SHA-256 staging identities.

Production `src/Phil/Core/BoundaryProgression.hs` is unchanged in this slice. A green staging run is mechanized evidence only; the ledger remains `Discharged / Certified` until a separate exact-kernel production-binding closeout.
