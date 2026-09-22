# Phase 1 audit — portable typed-support correspondence

This slice follows the `PHIL-AUDIT-20260922-DEPENDENCY-PORTABILITY-REUSE` handoff after the checker-to-manifest prerequisite-support binding landed in #1316.

It addresses the handoff's portable-preservation obligation only: the Phase 1 assurance-input format must retain the two evidence-dependency constructors as distinct relations with exact targets.

## Correspondence boundary

`Phase1AssuranceInputs` intentionally serializes two different support relations:

- `DependsOnEvidence evidence-id` names one exact selected evidence artifact;
- `DependsOnObligation revision-id` names a whole-obligation prerequisite whose revision-domain lookup is deferred to the accepting consumer.

The codec must not collapse either relation into the other. In particular, a precise helper evidence entry is not interchangeable with whole-target obligation closure, even when both happen to concern the same semantic target.

This slice does not establish evidence truth, does not invent a revision domain inside the evidence-only codec, and does not turn generation provenance into support. The accepting INT-002 path remains responsible for current bundle/ledger membership and revision-domain checks. LLVM and the other Phase 1 trusted-computing-base components are unchanged and out of scope.

## Permanent controls

`Phase1AuditPortableSupportCorrespondenceMain` checks that:

1. a selected evidence entry carrying both a precise `DependsOnEvidence` edge and a `DependsOnObligation` edge survives `derive -> render -> decode` exactly;
2. a precise evidence dependency cannot survive when its evidence target is omitted from the selected assurance inputs;
3. changing the serialized dependency constructor without rebinding the evidence digest fails closed; and
4. an obligation dependency remains an obligation dependency and does not become an evidence-selection requirement merely because the portable codec has no revision domain.

These controls are deliberately narrower than whole manifest closure. They establish typed portable content preservation while retaining the later consumer obligation identified by the audit handoff.
