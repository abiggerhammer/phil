# PHIL-SYS-GENERIC-001 — generic Systems lowering proof v1

This slice certifies the witness-neutral checked Architecture/Core → Systems producer introduced by PR #458.

## Claim

A checked Core input and explicit realization context determine the normalized Systems lowering result without dispatching on witness/program identity. The lowering preserves the exact architecture instance revision, keeps selected realization identity separate from source instance identity, and revises Systems identity when Core semantics, realization-context semantics, lowering decisions, or runtime-site bindings change.

The proof also composes the generic producer with the already Certified `PHIL-SYS-STAGE-CLOSURE-001` theorem: generic production does not replace bidirectional source-disposition / target-justification closure.

## Normalized model

`proof/Phil/Core/SystemsGenericLowering.v` models:

- `GenericCoreInput`: exact `ArchitectureInstanceIdentity` plus normalized Core semantic revision;
- `GenericRealizationContextFacts`: explicit context, verifier profile, realization-reference, decision, runtime-site, and realization-semantic revisions;
- structural source, Systems, and StageContract revisions;
- `lowerGenericSystemsModel`, which contains no witness/program discriminator;
- a witness adapter whose presentation label is erased before generic lowering.

Theorems establish:

1. deterministic lowering for fixed checked input and realization context;
2. witness presentation rename is nonsemantic;
3. exact architecture instance revision survives source and realization identity construction;
4. changing explicit realization semantics revises `ArchitectureRealizationRevision` while preserving the source instance revision;
5. Core semantic, realization-context, decision, and runtime-site changes revise the normalized Systems identity;
6. missing realization references or an empty verifier profile cannot be accepted;
7. certified generic lowering retains exact `SystemsStageClosurePreserved` closure.

## Haskell correspondence boundary

The Rocq model intentionally does not reproduce Haskell `Text`, `Map`, `Set`, canonical `SemanticForm` serialization, digest bytes, `systemsProgramDigest`, or concrete enumeration order. Those remain implementation correspondence boundaries.

The dedicated workflow therefore strict-typechecks and reruns the unchanged implementation/corpus from PR #458:

- `src/Phil/Systems/GenericLowering.hs`;
- `src/Phil/Examples/Phase1/SystemsWitnesses.hs`;
- `test/Phase1GenericSystemsLoweringMain.hs`;
- `test/Phase1GenericSystemsStageMain.hs`.

The correspondence corpus checks that framed upload and Steve both use the same generic producer/verifier path, presentation rename remains nonsemantic, one checked instance admits distinct explicit realizations, missing realization information fails closed, Steve's target-only ABI strengthening remains explicit, and both witnesses still satisfy the generic StageContract accounting substrate.

## Scope

This proof closes `PHIL-SYS-GENERIC-001` at the checked Architecture/Core → Systems boundary. It does **not** claim that arbitrary ordinary `.phil` source has completed the parser/elaborator/Core migration; that broader end-to-end witness remains tracked separately by `PHIL-P1-WITNESS-001`.
