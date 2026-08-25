# Phase 1 provider qualification dependency closure v1

This slice implements conformance case `PROV-012`: higher-level provider qualifications may depend on lower-level provider admissions, but qualification dependencies may not close by circular self-endorsement alone.

## Model

`ProviderQualificationDependencyGraph` contains three distinct things:

- a selected set of root `QualificationAdmissionRevision`s for the current closure check;
- exact admitted qualification nodes and their qualification-to-qualification dependencies; and
- an independent ground registry.

Independent grounds are explicitly typed as proof, runtime enforcement, external evidence, assumption, or TCB facts. Assumption and TCB grounds are conditional facts, not unconditional proof of their environments. What makes them grounds here is that their acceptance does not derive from the provider qualifications being closed by this graph.

Every referenced qualification admission and every referenced ground must exist exactly. A rejected admission cannot support another admission. A rejected ground cannot close a qualification dependency.

## Grounded cycles

Cycles are not rejected merely for being cycles. The Phase 1 rule is narrower: a cycle must not be its own only justification.

The checker computes the least fixed point of independently accepted grounds reachable through qualification dependencies. Therefore:

- `A -> proof` closes;
- `A -> B -> runtime-ground` closes and `A` retains the runtime ground transitively;
- `A <-> B` with no independent ground rejects as circular self-endorsement;
- `A <-> B` with an independently accepted assumption/proof/runtime/external/TCB ground feeding the SCC closes conditionally; and
- a self-cycle with no ground rejects.

The checked result retains, for every reachable admission, the complete transitive set of independent grounds that support it. This is intended to feed later reverse-dependency, assumption-retention, replacement, and StageContract checks.

## Root-scoped closure

Closure is checked only for admissions reachable from the selected roots. A long-lived registry may therefore contain stale or rejected unrelated admissions without invalidating a build that does not depend on them.

Registry key integrity is still checked globally: a map entry whose key disagrees with the semantic key carried by its value is malformed regardless of reachability.

## Deliberate limits

This slice does not establish the truth of proof/runtime/external/assumption/TCB grounds. Their truth and current policy acceptance are separate assurance responsibilities.

It also does not yet implement cross-target semantic qualification reuse (`PROV-013`), concrete artifact/profile applicability (`PROV-014`), replacement/evidence noninheritance (`PROV-015`), concrete Steve qualification artifacts (`PROV-016`), ArchitectureRealization selection, StageContract lowering, final source syntax, or Rocq proof.
