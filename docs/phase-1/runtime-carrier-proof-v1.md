# PHIL-ASSURE-CARRIER-001 — runtime carrier proof v1

This proof certifies the normalized semantic rule implemented by Matrix DEP-001 and DEP-002.

A `RuntimeEnforced` obligation may close only through an exact carrier binding. For every required retained-runtime use, the model requires one known carrier tied to the same obligation, one actual Systems runtime site carrying the exact selected runtime evidence/revision/cost identity, one process-local execution coverage relation, and complete RuntimeEnforced authority. The site also remains attached to the Certified Systems runtime claim/contribution/final-charge graph.

Every potentially violating use is accounted for as exactly one of:

- statically safe;
- covered by an exact carrier binding; or
- an explicit nonempty boundary.

Every active execution/domain transfer is explicitly accounted for as carrier preservation, replacement, discharge, or validity end. Preserve/replace retain exact obligation/process identity and required execution coverage; discharge/end-validity require that the destination no longer remains RuntimeBound. Missing bindings, phantom carriers, and incomplete runtime mechanisms cannot certify.

The theorem composes:

- `PHIL-ASSURE-EVID-001` (`proof/Phil/Assurance/EvidenceUse.v`) for complete RuntimeEnforced evidence authority; and
- `PHIL-SYS-RUNTIME-GRAPH-001` (`proof/Phil/Core/SystemsRuntimeGraph.v`) for selected runtime evidence, revision/cost exactness, and physical contribution/charge lineage.

The dedicated correspondence job reruns the unchanged DEP-001 and DEP-002 Haskell corpora under `-Wall -Werror`.

## Boundary

This is a semantic establishment/coverage theorem. It does not prove that a concrete hardware/runtime mechanism is physically sound, that scheduler/device behavior meets an unstated property, or that provider/platform evidence is true. Concrete Haskell Text/Map/Set representation and enumeration of potentially violating uses remain implementation-correspondence boundaries.
