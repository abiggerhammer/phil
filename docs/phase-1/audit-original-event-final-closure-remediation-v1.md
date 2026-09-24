# PHIL-AUD original check-event final closure remediation

This implementation slice follows the original-event forest repair and the live `PHIL-AUDIT-20260924-CONSUMER-ENDPOINT-COVERAGE` handoff. It closes one concrete integration gap without changing the Phase 1 trusted computing base or modifying Rocq.

## Problem

`resolveOriginalCheckEvent` and `handoffOriginalCheckEvent` now preserve the actual residualizing `ValueResult`, including a definitionally discharged parent whose partial-operation prerequisite remains runtime-bound. The final manifest consumer, however, still accepted a separately supplied `ManifestClosureHandoff`. A caller could therefore use the repaired event adapter to inspect the right forest and then close a bundle using an independently reconstructed smaller handoff.

The final accepting entry must consume the event-derived forest itself.

## Repair

`Phil.Assurance.closeOriginalCheckEventBundle` takes the actual `ValueResult`, exact `ResidualSpec`, discharge policy, verification bundle and final assurance inputs. It derives the handoff from that same event and passes it directly to `closeVerificationBundleWithHandoff`; callers do not supply the handoff forest.

The downstream closure therefore continues to enforce exact revision identity, semantic support edges, final certification-scope support, and immutable final evidence-domain checks on the forest produced from the actual event.

This first adapter is deliberately bounded. It supplies no local `EvidenceFact` identity map, so an event that actually needs certificate-local evidence authority fails closed at handoff instead of inferring authority from a name or fact index. Direct named evidence likewise remains subject to the existing immutable-authority final checks. The already-existing authority-aware evidence routes remain separate until the complete actual-use/subject inventory is connected explicitly; this slice does not manufacture that correspondence.

## Permanent replay

The existing `Phase 1 Audit Original Event Forest` regression now adds two final-consumer controls:

1. the actual checker result for `(a-b)==(a-b)` closes through the event-derived parent-to-runtime-prerequisite forest; and
2. the same bundle with that support edge removed is rejected by final manifest closure because the adapter re-derives the complete event handoff rather than accepting the smaller graph as authority.

The preceding six controls remain unchanged in purpose, including exact occurrence/scope rejection, dropped-residual rejection, and the valid `(5-3)==(5-3)` static control.

## Preserved boundaries

This change does not reject products, alter product definitional equality, require refinements to be inhabited at formation, merge logical binders with ambient resource/proof names, or restore consumed affine/linear ownership. It does not modify proof-only or Rocq work.

The live audit's broader correspondence remains explicit: complete enumeration/classification of all actual evidence uses and all relevant subject occurrences still has to be bound to the same final consuming operation. Closed facts need a checked closed-use classification rather than an incidental missing subject mapping. That is a successor implementation task, not something this adapter claims to prove.