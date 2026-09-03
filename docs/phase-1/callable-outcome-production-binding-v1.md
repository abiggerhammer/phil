# Callable Outcome production binding v1

`PHIL-CALL-OUTCOME-001` is production-bound to the exact Rocq-extracted `CallableOutcomeKernel.hs` staged by PR #633.

## Exact kernel identity

- staging exact green head: `d076e22ec875d9b99d0770672b9a9047ca145931`
- staging merge: `643c1361d85426e434641c4566a427ab4534b171`
- staging run: `33801028670`
- staging artifact: `9911110069`
- artifact digest: `sha256:0fab1bcc36a9a297146ef8c2c490673dea54f522d75c1f49173d2d94cf80b725`
- exact kernel SHA-256: `bd25c94d9240bdf3c32ff402ddd39c826f9e478d413264975353955eb7ac9f8f`
- exact kernel Git blob: `ea1b5afb4db8fb6ae310f6d5f622509cb13c8abb`

The generated and source-tree kernel copies are byte-identical to the staging artifact. The production workflow freshly regenerates the kernel from Rocq and byte-compares both checked-in copies before any Haskell binding evidence is accepted.

## Extracted semantic ownership

The exact kernel owns the final CALL-018 semantic classification over reflected facts, in Certified precedence:

1. exact outcome-class domain;
2. exact branch-sensitive state;
3. exact callee transition;
4. residual-obligation reclassification or mismatch disposition;
5. exact residual-obligation set;
6. exact postconditions;
7. exact assumptions;
8. exact effects;
9. exact discharged facts;
10. acceptance only after every preceding fact is exact.

Production `Phil.Core.CallableOutcome` computes the concrete Haskell facts and residual witness, submits those facts to the extracted classifier, and reconstructs the existing payload-bearing diagnostic only when the classifier result agrees with the concrete native facts. An impossible disagreement becomes `CallableOutcomeKernelDisagreement`; handwritten code may therefore fail closed but cannot override an extracted rejection into success.

## Native boundary retained

The following remain native and explicit correspondence/predecessor boundaries:

- `CallableOutcomeClass`, `CallableOutcomeState`, `CallableOutcomeAtom`, `CalleeTransition`, and `Text` representation/equality;
- list-to-`Map` normalization and duplicate detection;
- `Map`/`Set` construction, equality, membership, ordering, difference, and traversal semantics;
- selection of the first concrete missing residual-obligation witness and the native bucket-membership probes used to reflect its disposition;
- construction of `CheckedCallableOutcomeContract`;
- exact native diagnostic payload values and outer branch traversal order;
- source elaboration and the truth/competence of proposition/evidence facts represented by stable outcome atoms;
- GHC/runtime correctness and the Rocq extraction toolchain.

## Closeout gate

The production gate:

- freshly compiles the Certified and implementation Rocq files;
- freshly extracts the kernel and requires SHA-256 `bd25c94d9240bdf3c32ff402ddd39c826f9e478d413264975353955eb7ac9f8f`;
- byte-compares both checked-in kernel copies;
- strictly typechecks the kernel, bridge, production checker, direct correspondence harness, production-binding harness, and unchanged CALL-018 corpus;
- executes all fourteen direct extracted-kernel controls;
- executes eighteen production-binding controls;
- reruns the unchanged ten-case CALL-018 corpus.

A fully green merge promotes `PHIL-CALL-OUTCOME-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
