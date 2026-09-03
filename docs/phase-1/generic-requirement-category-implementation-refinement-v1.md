# Generic Requirement Category implementation refinement v1

`PHIL-GEN-CATEGORY-001` is already Certified by `proof/Phil/Core/GenericRequirementCategory.v`. This staging tranche adds an executable correspondence layer without changing production `Phil.Core.Generic.RequirementCategory`.

## Extracted semantic seam

`proof/Phil/Core/GenericRequirementCategoryImplementation.v` exposes three representation-neutral executable surfaces:

1. the Certified `competenceForRequirementCategory` mapping for all thirteen generic requirement categories;
2. `decideRequirementHandoffByFacts`, which accepts only when the handoff key/category/target and the checked key/category/semantic payload/competence all exactly match the Certified requirement; and
3. `decideRequirementInterfaceDomainByFacts`, which accepts only when both the handoff domain and checked-result domain exactly equal the public requirement domain.

The handoff decision preserves fail-closed precedence across key, category, target, checked-key, checked-category, checked-semantic-form, and checked-competence mismatches. The target fact is exact equality with `GenericHandoffToCompetence (competenceForRequirementCategory category)`, so an assumption target or a wrong competent checker cannot satisfy it.

The correspondence theorem proves executable handoff acceptance iff Certified `RequirementHandoffAccepts`, under explicit reflection hypotheses for the native equality facts. A second theorem proves interface-domain decision acceptance iff the two exact Certified domain relations. Certified `CheckedGenericRequirementInterfaceValid` supplies both domain relations.

## Staging validation

`app/GenericRequirementCategoryDecisionCorrespondenceMain.hs` directly exercises twenty-four extracted controls:

- all thirteen category-to-competent-checker mappings;
- exact handoff acceptance;
- each of the seven ordered handoff mismatch classes; and
- exact-domain acceptance plus handoff-domain and checked-domain rejection.

The dedicated workflow recompiles the Certified proof and executable correspondence under Rocq 9.2.0, fresh-extracts `GenericRequirementCategoryKernel.hs`, records exact identities, strict-typechecks and executes the extracted controls under GHC 9.6.7, then strict-typechecks unchanged production and reruns the unchanged six-case GEN-014 corpus.

## Explicit representation boundary

This staging tranche deliberately leaves production unchanged. The following remain native foundations for the later production binding:

- concrete `GenericRequirementKey` / `Text` and `SemanticForm` equality;
- `Map`/`Set` normalization, duplicate detection, exact domain construction, traversal, and ordering;
- native diagnostic payloads and rejection distinctions;
- construction of `CheckedGenericRequirementHandoff` values; and
- truth and competence of each category-specific downstream checker.

A green staging merge leaves `PHIL-GEN-CATEGORY-001` at `Discharged / Certified`. Promotion to `Implementation Refined` requires checking in the exact extracted kernel and routing production final acceptance through it with fail-closed native bridges.
