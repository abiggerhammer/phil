# Provider lineage core production binding v1

`PHIL-PROV-LINEAGE-CORE-001` is mechanically bound to the exact Rocq-extracted decision kernel staged by #483.

## Exact kernel

The checked-in production copy is:

`src/ProviderQualificationLineageCoreKernel.hs`

with SHA-256:

`88efd406ce0e79d763c185e5ffc67665882694dd02491f2892699e0d17f7d4c5`

The lineage-core workflow fresh-extracts the kernel from `ProviderQualificationLineageCoreImplementationExtraction.v`, verifies that digest, and byte-compares the fresh extraction with the checked-in copy.

## PROV-011 identity binding

`Phil.Core.ProviderQualificationIdentity` keeps canonical `SemanticForm` construction and revision construction native. Admission checking reflects the four Certified identity facts into `decideQualificationIdentityByFacts` in Certified gate order:

1. evidence binds the exact claim revision;
2. admission binds the exact claim revision;
3. admission binds the exact evidence revision; and
4. admission requires the exact semantic interface.

The kernel decision is translated back into the pre-existing Haskell diagnostic constructors, preserving concrete expected/actual revisions and interface values.

The evidence-only checker uses the same kernel with only its evidence/claim fact open and the downstream admission facts fixed true.

## PROV-012 dependency binding

`Phil.Core.ProviderQualificationDependency` retains finite `Map`/`Set` representation, deterministic ordered traversal, reachable-node enumeration, exact diagnostic payload construction, and fixed-point scheduling/stability equality as explicit representation bridges.

Semantic admission decisions are kernel-owned at the existing traversal points:

- node and ground registry-key equality use `decideQualificationRegistryByFacts`;
- selected-root existence uses `decideQualificationRootByFacts`;
- rejected admissions, unknown admission dependencies, unknown grounds, and rejected grounds use `decideQualificationDependencyNodeByFacts`; and
- final all-reachable grounding uses `decideQualificationDependencyClosureByFacts`.

Ground propagation is bound per ground key. For every key in the finite ground registry, production reflects whether the current admission already has that ground and whether each reachable dependency currently has it into `propagateGroundPresence`. The resulting true keys reconstruct the next `Set`. This is extensionally the prior `own ∪ inherited` step while leaving finite key enumeration and iteration scheduling native.

## Residual boundary

This closeout does not claim to verify canonical serialization or revision hashing, `Text`/`Map`/`Set` representation correspondence, registry enumeration, fixed-point scheduling or equality, diagnostic payload construction, or the truth and validity scope of independent proof/runtime/external/assumption/TCB grounds. Those remain explicit correspondence or evidence boundaries. PROV-013 cross-target reuse and PROV-014 concrete applicability remain separate obligations.
