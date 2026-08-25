# Phase 1 provider state simulation v1

This slice advances `PHIL-PROV-QUAL-001` with conformance case `PROV-006` from the Provider Qualification Checking and Schema Contract.

## Boundary

The stateless provider-qualification kernel from #178 established exact provider/implementation identity, total public operation correspondence, per-operation callable refinement, explicit implementation-outcome to public-outcome mapping, and exact resource residue.

This slice adds the stateful whole-provider condition required before those operation refinements may be treated as a provider-state simulation.

The governing rule is:

> Every implementation state from which the provider can become client-visible must correspond to an admissible abstract initial state, and every reachable implementation transition from a related state must simulate an allowed abstract transition while preserving the named state relation.

## Named state relation

`ProviderStateRelationRevision` names one exact provider-state relation `α : J ~ A`.

The checker-facing relation is represented extensionally by `ProviderStatePair` values connecting implementation-state keys to abstract-state keys. This is deliberately not a universal theorem language. A later proof or qualification artifact may establish the same relation by symbolic reasoning, proof assistant theorem, model checking, or another accepted method.

The relation revision is retained in the checked result together with the exact provider contract `InterfaceRevision` and implementation `DefinitionRevision` inherited from the already-accepted semantic qualification.

## Initialization

The state refinement records separately:

- every implementation state from which the provider may initially become client-visible;
- every admissible abstract initial state; and
- an exact implementation-initial-state → abstract-initial-state mapping.

The mapping domain must exactly equal the visible implementation initial-state set.

Each mapped abstract state must be admissible, and each mapped pair must belong to the named state relation.

A provider cannot qualify transitions while leaving its client-visible initial state outside or undefined by the abstract state model.

## Transition simulation

Every reachable implementation transition records:

- the already-qualified public provider operation;
- implementation pre-state;
- implementation outcome key; and
- implementation successor state.

The implementation outcome is interpreted only through the exact outcome correspondence already accepted by `PROV-001–005`. The implementation cannot use a private outcome name as though it were the public contract outcome.

For each abstract state related to the implementation pre-state, the checker requires an allowed contract transition with:

- the same public provider operation;
- that exact related abstract pre-state;
- the public outcome corresponding to the implementation outcome; and
- an abstract successor related to the implementation successor state.

Thus if one concrete state is related to multiple abstract states, the concrete transition must simulate the contract from every one of those related abstract possibilities. The checker does not select the most convenient relation witness.

## Asymmetry

Simulation is intentionally asymmetric.

The provider contract may allow abstract behaviors that the implementation never exercises. A narrower implementation is therefore acceptable.

The reverse is not true: every reachable implementation transition must be represented by the public operation/outcome model and preserve the relation.

## Conformance coverage

The dedicated harness covers:

- a valid stateful provider simulation;
- missing and unexpected visible-initial-state mappings;
- inadmissible abstract initial state rejection;
- initialization pairs outside the named relation;
- transitions using operations absent from the accepted provider qualification;
- implementation outcomes absent from the accepted outcome correspondence;
- reachable implementation pre-states outside the relation;
- missing abstract transition simulation;
- successor implementation states outside the relation;
- explicit use of the mapped public outcome rather than private implementation outcome identity;
- acceptance of an implementation that realizes fewer abstract transitions;
- simulation of every abstract pre-state related to one implementation state; and
- ordering/canonicalization noninterference.

## Deferred

This slice does not yet claim:

- provider-wide cross-operation laws (`PROV-007`);
- lifecycle/crash/interruption semantics (`PROV-008`);
- provider/foreign authority confinement (`PROV-009` / `AUTH-006`);
- evidence-producer subject competence (`PROV-010`);
- symbolic or universal theorem syntax for provider-state relations;
- interference-model or persistence assumptions;
- qualification evidence/admission closure;
- ArchitectureRealization provider selection;
- final source syntax; or
- Rocq proof of the provider-state simulation obligation.
