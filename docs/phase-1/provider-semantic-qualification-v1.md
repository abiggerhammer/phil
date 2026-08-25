# Phase 1 provider semantic qualification v1

This slice begins `PHIL-PROV-QUAL-001` and covers conformance cases `PROV-001` through `PROV-005` for the bounded stateless provider fragment.

## Boundary

A provider qualification is an explicit semantic refinement claim. It is not inferred from source names, exported symbols, ABI signatures, method-set resemblance, successful linking, or tests.

This first implementation slice establishes the operation-level semantic kernel used by later whole-provider qualification.

It deliberately does not yet model provider-wide state, laws, lifecycle/crash properties, authority confinement evidence, evidence-producer competence, conditional dependencies, qualification evidence bundles, or build admission.

A stateless pure-Phil provider with no additional provider-wide obligations can close this bounded semantic qualification directly.

## Provider contract and implementation

`ProviderContract` carries:

- the exact public provider `InterfaceRevision`; and
- the exact map of public provider operations.

Each `ProviderOperationContract` carries:

- the public callable refinement surface;
- client-visible preconditions; and
- exact per-outcome resource residues.

`ProviderImplementation` carries:

- the exact semantic implementation `DefinitionRevision`;
- implementation operation entries; and
- optional implementation symbols as nonsemantic metadata.

Symbols are intentionally ignored by the checker.

## Total explicit operation correspondence

`ProviderQualificationClaim` must contain exactly one correspondence entry for every public provider operation and no correspondence for an operation absent from the public contract.

Each `ProviderOperationCorrespondence` names an exact implementation entry and an explicit implementation-outcome to contract-outcome map.

Two public operations may refer to the same implementation entry when that relation is explicit. No relation is synthesized from equal names, ABI shapes, symbols, or vtable positions.

## Per-operation refinement

For each public operation, the checker:

1. resolves the explicit implementation entry;
2. applies the already-landed callable refinement relation;
3. rejects any implementation precondition absent from the public contract;
4. requires every implementation outcome to have an explicit public-outcome correspondence;
5. rejects mappings to nonexistent public outcomes; and
6. requires exact resource residue equality for every mapped implementation outcome.

Callable refinement already provides the bounded Phase 1 checks for:

- no stronger caller authority requirement;
- no wider semantic effect bound;
- no additional modeled/fatal failure; and
- compatible callee lifecycle.

An implementation may have a narrower effect or failure surface. Public provider semantics remain unchanged.

## Resource residues

`ProviderResourceResidue` keeps these resource categories distinct:

- borrowed inputs;
- consumed inputs;
- returned predecessor resources;
- successor resources; and
- newly produced resources.

A nominally equal output cannot therefore hide a borrow/consume/return/successor mismatch.

The v1 relation requires exact residue equality for each mapped implementation outcome. More general resource refinement may later be expressed through an explicit checked adapter, never by nominal type coincidence.

## Conformance coverage

The dedicated harness covers:

- valid stateless pure-Phil semantic qualification (`PROV-001`);
- missing and unexpected public operation mappings (`PROV-002`);
- matching implementation symbols with no semantic mapping (`PROV-002`);
- unknown implementation entries;
- stronger implementation preconditions (`PROV-003`);
- stronger caller authority through callable refinement (`PROV-003`);
- narrower effect/failure implementations (`PROV-004`);
- wider effects and undeclared fatal outcomes (`PROV-004`);
- missing outcome mappings;
- mappings to nonexistent public outcomes;
- resource residue mismatch (`PROV-005`);
- exact provider contract and implementation revisions;
- canonical correspondence ordering; and
- symbol-name noninterference.

## Deferred

This slice does not yet claim:

- provider-state initialization/transition simulation (`PROV-006`);
- cross-operation provider laws (`PROV-007`);
- lifecycle/crash refinement (`PROV-008`);
- provider authority confinement and rich-internal projection (`PROV-009` / `AUTH-006`);
- evidence-producer subject competence (`PROV-010`);
- qualification claim/evidence/admission revision derivation;
- conditional qualification closure;
- contextual build admission;
- ArchitectureRealization provider selection;
- concrete artifact/ABI qualification;
- final syntax; or
- Rocq proof.
