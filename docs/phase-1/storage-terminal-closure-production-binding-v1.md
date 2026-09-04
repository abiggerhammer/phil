# Storage Terminal Closure production binding v1

`PHIL-MEM-CLOSURE-001` was Certified by the Storage Terminal Closure proof and its representation-neutral executable surface was staged by PR #674. This closeout binds production storage/process terminal acceptance to the exact extracted kernel without collapsing semantic storage closure into physical reclamation.

## Exact kernel

The checked-in copies are byte-identical to the #674 extraction artifact:

- `generated/StorageTerminalClosureKernel.hs`
- `src/StorageTerminalClosureKernel.hs`
- SHA-256: `d3e81f48655c7318deba59baad788f0009f42a3bf422487cab64f47edb1f4476`

The kernel exposes ten gates: three semantic-owner cases, semantic-owner aggregate closure, three physical-state cases, physical aggregate reclamation, process memory closure composition, and root memory closure composition.

## Production composition

`Phil.Systems.StorageTerminalClosureCertification` preserves the existing native checkers and their diagnostic order.

### Semantic storage closure

`checkSemanticStorageTerminalClosureCertified` first calls the unchanged `checkSemanticStorageTerminalClosure`. Only after native success does it independently reflect:

- exact per-owner state (`live`, `released`, or terminal disposition);
- exact terminal-disposition permission membership;
- uniqueness of semantic storage owner keys;
- acceptance of every reflected owner state.

It then requires the exact per-owner extracted gate and aggregate semantic-closure gate. A native-success/kernel-reject disagreement fails closed with the reflected facts.

### Physical reclamation

`checkPhysicalStorageReclamationCertified` first calls the unchanged `checkPhysicalStorageReclamation`. Only after native success does it independently reflect:

- reclaimed, leaked, or profile-retained physical state;
- whether retention is permitted by policy;
- exact expected/actual profile equality;
- uniqueness of physical object keys;
- acceptance of every reflected physical state.

It then requires the exact per-state and aggregate physical-reclamation gates. Physical reclamation remains a realization/profile obligation and is not used as a Phil semantic-terminal premise.

### Process storage composition

`certifyMemoryProcessStorageClosure` composes three real production predecessors before requiring the extracted process-memory gate:

1. `verifyStageClosureBundle` (already kernel-gated StageClosure);
2. `checkStorageRealizationCertified` (implementation-refined MEM-001);
3. `checkSemanticStorageTerminalClosureCertified`.

The ordinary process-terminal theorem remains the separate predecessor represented by the Certified `ProcessTerminalFact` parameter in the Rocq statement; this wrapper binds the additional storage-specific fields rather than reconstructing ordinary process terminality.

### Root terminal composition

`classifyProcessNetworkWithStorageCertification` calls native `classifyProcessNetwork` first. Native lifecycle/root diagnostics therefore keep precedence. Only when native classification returns `NetworkTerminal` does the wrapper:

1. require the runtime-status domain to equal the declared process population;
2. certify semantic storage closure for every static process;
3. require the exact extracted root-memory closure gate.

There is deliberately no physical-reclamation argument to this API. A later physical leak may fail realization/profile certification but cannot retroactively rewrite an already-established Phil semantic root-terminal fact.

## Retained boundaries

The kernel does not prove or replace:

- Haskell `Text`, `Map`, `Set`, or list representation;
- finite enumeration completeness outside the concrete checked maps/lists;
- truth or provenance of storage disposition permissions;
- truth or authority of target reclamation profiles;
- provider/allocator reclamation behavior;
- ordinary process-terminal provenance outside the existing lifecycle/certification chain;
- canonical hashing, compiler/extraction correctness, GHC correctness, or runtime correctness.

Native validation remains intentionally at least as strict as the normalized proof model (for example, production rejects empty concrete identities even where the normalized closure theorem only reasons about exact identity equality/uniqueness).

## CI closeout

The dedicated production-binding workflow must:

- freshly compile the Certified Rocq predecessor chain and implementation correspondence;
- freshly extract `StorageTerminalClosureKernel.hs`;
- require the exact SHA-256 above and byte-compare both checked-in copies;
- build the broad Haskell regression surface;
- strictly typecheck native storage/lifecycle code, refined predecessors, the new bridge, and production controls;
- rerun the ten-gate direct extracted-kernel controls;
- rerun implementation-refined MEM-001 and MEM-002/003 production controls;
- execute production binding controls including real process/root terminal fixtures;
- rerun the unchanged MEM-001--006 and process-terminal corpora.

A green exact-head merge promotes `PHIL-MEM-CLOSURE-001` from **Certified** to **Implementation Refined**. `PHIL-MEM-COST-001` remains a separate Certified refinement target.
