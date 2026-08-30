# Boundary progression production binding v1

`PHIL-BND-PROGRESS-001` is already Certified by `proof/Phil/Core/BoundaryProgression.v`.
PR #433 staged an executable representation-neutral correspondence layer and extracted `BoundaryProgressionKernel.hs` without changing production. This closeout binds production to that exact extracted kernel.

## Exact kernel

Production checks in `src/BoundaryProgressionKernel.hs` byte-for-byte from the #433 extraction:

`sha256:afa650e93d6f954e71efb6283aa0bda6b342da37a7426fcc80adee02ea0848db`

The production-binding workflow fresh-extracts the same kernel and requires byte identity plus the exact SHA before testing the bound production path.

## Bound production surface

`src/Phil/Core/BoundaryProgression.hs` retains its public Haskell API and diagnostics.

Receive progression reflects concrete grammar/value equality plus the result of the existing underlying `commitReceive` step into `decideReceiveProgressionByFacts`. The extracted decision preserves the Certified gate order: grammar identity, source-value identity, then underlying progression acceptance. Haskell laziness means the underlying receive result is demanded only after both identity gates pass.

Complete-emission establishment keeps concrete `Int` classification native. The native classifier maps the observed extent to the Certified four-way `EmissionDisposition`; `decideEmissionDisposition` owns the semantic accept/reject choice. Accepted completion evidence is reconstructed only through extracted `planCompleteEmission`, preserving the exact generated representation and output owner.

Send progression reflects concrete representation/owner equality plus the result of the existing underlying `sendEndpoint` step into `decideSendProgressionByFacts`. The extracted decision preserves the Certified gate order: representation identity, output-owner identity, then underlying progression acceptance. The underlying send result is demanded only after both identity gates pass.

## Explicit native boundaries

This binding does not move the following claims into Rocq:

- concrete Haskell `Int` extent arithmetic, including negative and overflow behavior;
- byte-count observation and transport-completion truth;
- actual wire I/O and provider/target transport behavior;
- concrete `Name` and `BoundaryRepresentationId` equality;
- truth of parsed, correspondence, generated-encoding, and completion evidence supplied by predecessor obligations;
- correctness of the underlying `commitReceive` and `sendEndpoint` implementations; or
- native error/result reconstruction.

Rocq extraction/toolchain correctness and the GHC/Haskell runtime remain TCB components.

## Closeout criterion

The exact-head workflow must:

1. compile the Certified proof and implementation correspondence;
2. fresh-extract the kernel and compare it byte-for-byte with production;
3. assert the exact harvested kernel SHA;
4. strict-typecheck the checked-in kernel and bound production path under `-Wall -Werror`;
5. rerun the unchanged direct extracted-kernel controls;
6. rerun the unchanged four-case BND-011 production corpus; and
7. record exact closeout identities as workflow artifacts.

Only after that exact-head matrix is green may the ledger advance `PHIL-BND-PROGRESS-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
