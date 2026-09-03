# PHIL-DATA-SUM-001 — implementation refinement staging

This staging slice turns the Certified resource-bearing-sum semantics into a small executable kernel without changing production Haskell behavior.

## Staged executable surface

`proof/Phil/Core/DataSumImplementation.v` exposes four executable decisions:

1. constructor selection accepts only after native constructor/tag lookup establishes that the selected payload is declared;
2. selected-payload restoration accepts only when the aggregate was actually consumed and the selected constructor-local payload was restored exactly;
3. a continuing arm accepts only after the selected payload satisfies the Certified elimination discipline; and
4. branch convergence accepts only when ordinary resource join succeeds and the branch state is either already structurally compatible or has been made explicit through a common checked sum/option/state package.

`proof/Phil/Core/DataSumImplementationExtraction.v` extracts those decisions as `DataSumKernel.hs` in CI. `app/DataSumDecisionCorrespondenceMain.hs` exercises 15 direct controls over the extracted artifact.

## Deliberate native boundaries

The kernel does not manufacture or reinterpret:

- source constructor names, tags, ordering, exhaustiveness, or selected payload metadata;
- concrete `Name`, `Ty`, `Map`, or `ResourceContext` representations;
- actual aggregate consumption or constructor-local successor insertion;
- the already-refined conservative structural-mode calculation from `PHIL-DATA-MODE-001`;
- ordinary `joinContinuing` / resource-join acceptance;
- the identity/type of an explicit branch-state package; or
- concrete diagnostics and source locations.

Those facts remain native. The extracted decisions are fail-closed gates over facts established by the existing implementation.

## Staging gate

The dedicated `Phase 1 Data Sum Proofs` workflow:

- compiles the existing Certified proof plus this implementation-correspondence layer under Rocq 9.2.0;
- freshly extracts `DataSumKernel.hs` and records its exact SHA-256 with the proof artifact;
- compiles and executes the 15 direct extracted-kernel controls under `-Wall -Werror`; and
- reruns the unchanged DATA-007/008/013 correspondence corpus: conservative sum mode, consuming sum match, continuing-arm linear cleanup, and explicit branch-resource packaging.

A green staging merge leaves `PHIL-DATA-SUM-001` at `Discharged / Certified`. Production binding and exact-byte closeout are required before promotion to `Implementation Refined`.
