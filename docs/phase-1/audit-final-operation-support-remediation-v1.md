# Phase 1 audit remediation: final operation support closure

Lineage: `PHIL-AUD-PREREQUISITE-SUPPORT-001` / `D-RES-GRAPH-CLOSURE-01`, continuing the retained-definedness-support repair after #1357.

## Problem

The resolver and checker-to-assurance handoff already preserve a direct prerequisite required by a locally credited operation, including the subtraction definedness condition for a parent discharged by `StaticByDefinition`. The verification graph also carries the same exact parent-to-prerequisite edge.

Before this repair, `closeVerificationBundleWithHandoff` checked that handoff support and graph support agreed, but final evidence fixed-point checks applied only to certificate and direct named-evidence parents. A definitionally discharged parent could therefore remain in the local certification scope while its required `RuntimeBound` prerequisite was exported. The intermediate edge was correct, but the final accepting boundary did not enforce it.

## Repair

The mandatory handoff-aware closure now treats retained support for a locally scoped `StaticByDefinition` consumer as an operation-support contract. For every exact retained edge `(consumer, prerequisite)`, if the consumer is definitionally discharged and credited in the local certification scope, the prerequisite must also remain in that scope.

The repair is deliberately bounded. Certificate consumers continue to use immutable certificate-evidence fixed points, and direct `StaticByEvidence` consumers continue to use their exact direct-evidence authority map. No decision certificate is fabricated for definitional truth, generation lineage is not reinterpreted as semantic support, and resource ownership is unchanged.

## Preservation

The full-scope definitional case remains valid: `(a - b) == (a - b)` may still close by definition while its declared subtraction side condition remains a `RuntimeBound` prerequisite in the same local scope. A definition with no retained prerequisite is unaffected. A consumer not claimed in the local certification scope is not constrained by this local-credit rule.

This does not reject products, change product definitional equality, require refinement predicates to be true at formation, or restore consumed resources. Certificate and direct named-evidence behavior remains on its existing paths.

## Permanent replay

`test/Phase1AuditFinalOperationSupportMain.hs` uses the real resolver to construct the definitional subtraction case and checks both sides of the boundary:

- the exact full-scope parent/prerequisite composition still closes successfully; and
- keeping the definitional parent local while exporting its retained runtime prerequisite fails with `ManifestClosureHandoffRequiredSupportOutOfScope` naming the exact parent and prerequisite revisions.

The existing definedness-support and handoff suites continue to cover producer support, graph correspondence, certificate finalization, and unchanged resolver/handoff behavior.
