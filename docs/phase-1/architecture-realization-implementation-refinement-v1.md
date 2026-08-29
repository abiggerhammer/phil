# Phase 1 Architecture Realization Implementation Refinement v1

Status: **staging — production unchanged**

Obligation: `PHIL-ARCH-REALIZE-001`

This slice stages the architecture-owned construction half of the already-Certified realization theorem. It does not change production behavior and it does not re-prove provider-replacement semantics.

## Certified construction coordinates

`ArchitectureRealization.v` defines one realization revision from exactly:

1. the exact `InstanceKey` of the abstract architecture occurrence;
2. the exact `InstanceRevision` of that occurrence; and
3. the selected realization semantics.

`ArchitectureRealizationImplementation.v` extracts that dependency shape as a polymorphic `ArchitectureRealizationPlan`. Its correspondence theorem shows that the three plan fields are exactly the three fields of Certified `deriveArchitectureRealizationRevision`.

The plan deliberately has no concrete namespace or serialization fields. The Certified theorem does not own Haskell's `phil.realization.canonical.v1:` prefix, `SemanticForm` record spellings, `Text` encoding, or concrete revision bytes. Those remain explicit native representation foundations for a later production binding.

## Provider replacement remains a separate refinement dependency

The broader `PHIL-ARCH-REALIZE-001` theorem also composes with Certified `PHIL-PROV-REPLACE-001` to require exact instance-revision preservation, fresh realization/qualification/evidence/admission lineage, rejection of topology-changing replacement, and explicit scoped reuse of shared evidence.

`PHIL-PROV-REPLACE-001` is currently Certified but not implementation-refined. This staging PR therefore does **not** upgrade the ARCH-REALIZE ledger row. After this construction plan is harvested, the row remains `Discharged / Certified` until the provider-replacement production correspondence and final realization binding are closed.

## Native boundaries retained

- Haskell `InstanceKey`, `InstanceRevision`, `SemanticForm`, and `Text` representation;
- canonical `SemanticForm` serialization and the concrete realization namespace/field spellings;
- collision-freedom/injectivity assumptions of concrete revision encoding;
- concrete provider artifact identity and provider-admission evidence;
- production correspondence for `PHIL-PROV-REPLACE-001`.

## Validation

The dedicated workflow:

- recompiles the existing Certified ARCH-ID, ARCH-INST, PROV-REPLACE, and ARCH-REALIZE proof chain with Rocq 9.2.0;
- compiles the construction-plan correspondence proof;
- fresh-extracts `ArchitectureRealizationKernel.hs`;
- strict-typechecks and executes direct plan controls;
- strict-typechecks unchanged production `Phil.Core.Static` and the unchanged ARCH-010 corpus; and
- reruns all 12 existing ARCH-010 cases unchanged.

An all-green exact head is staging evidence only. Production remains unchanged in this PR.
