# PHIL-DATA-SUM-001 — production binding

This closeout binds the exact `DataSumKernel.hs` staged by #610 to the production Phase 1 resource-bearing-sum ownership points.

## Exact staged identity

- staging PR: #610
- exact green staging head: `41d987192285d56c2b899ba86257f6b2d3cfc372`
- staging merge: `58b925d158a129e09beeac033f378de65c7bf688`
- Phase 1 Data Sum Proofs run: `33725411039`
- staging artifact: `9881845235`
- staging artifact digest: `sha256:41d332bb4ef3fe77fe3f32dce668b2765851ff0af2ec0ea7c5e7dcaeddbe1ce2`
- exact `DataSumKernel.hs` SHA-256: `7e04187772d0214e4e9edc424ae41b44843287d7fbf4bcfdc8c400b60747caf2`

`generated/DataSumKernel.hs` and `src/DataSumKernel.hs` are byte-identical copies of that extracted artifact. The production-binding workflow freshly re-extracts the kernel and requires both checked-in copies to compare byte-for-byte.

## Production ownership split

`Phil.Core.DataSum` is a narrow orchestration layer. It does not replace the lower-level semantics already refined elsewhere:

1. constructor/tag lookup remains native and selects the exact declared `OwnedField` payload; the certified constructor-selection decision must agree before success;
2. selected-payload matching delegates actual aggregate consumption and exact successor restoration to the already-bound `DataDestruction.consumeAggregateFields`; successful lower-level refinement is the fact supplied to the certified selected-payload restoration decision;
3. continuing-arm completion remains the native `ResourceContext.ensureComplete` boundary; successful completion is checked against the certified selected-payload accounting decision;
4. branch reconvergence remains native `ResourceContext.joinContinuing`; the production layer derives raw linear-shape compatibility from the actual branch contexts and, for explicit packaging, verifies the named linear package is present with the exact type on every predecessor before supplying those facts to the certified branch-convergence decision; and
5. conservative whole-sum structural mode remains owned by the already-refined `DataMode.deriveSumMode` path and is regression-tested here rather than duplicated.

Native failure always wins. Kernel disagreement can only reject.

## Deliberate native boundaries

The following remain outside the extracted kernel:

- source constructor names/tags, ordering, exhaustiveness, and source locations;
- concrete `Name`, `Ty`, `Map`, and `ResourceContext` representation;
- actual aggregate ownership consumption and successor insertion;
- actual branch package identity/type and package construction;
- ordinary join diagnostics and all other concrete diagnostics; and
- source elaboration that determines which constructor or explicit branch-state package applies.

## Closeout gate

The `Phase 1 Data Sum Production Binding` workflow:

- freshly extracts and hashes the exact kernel under Rocq 9.2.0;
- compares fresh extraction byte-for-byte with both production copies;
- builds the ordinary library with `-Werror` as a broad regression gate;
- strict-typechecks the bound Data Sum surface with `-Wall -Werror`;
- runs all 15 direct kernel controls through `src/DataSumKernel.hs`;
- runs production-path controls covering conservative mode, exact constructor selection, unknown constructor rejection, consuming payload restoration, empty constructors, continuing-arm cleanup, raw branch mismatch, and explicit package reconvergence; and
- reruns the unchanged DATA-007/008/013 correspondence corpus.

A fully green merge closes `PHIL-DATA-SUM-001` as `Discharged / Implementation Refined`.
