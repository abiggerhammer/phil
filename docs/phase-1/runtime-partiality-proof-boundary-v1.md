# PHIL-SYS-PARTIALITY-001 proof boundary

This slice certifies the Phase-1 target-independent runtime partiality relation.

## Certified semantic surface

For every classified lower-level hazard:

- the hazard's target precondition must already be a live, valid target
  strengthening fact;
- the exact `(target precondition, partiality consequence)` pair is semantic
  identity, so a trap cannot be replaced by an exceptional halt, a capacity
  class cannot collapse into another, and missing dispositions do not disappear;
- every live hazard has exactly one disposition;
- mapping to a source outcome requires that exact declared source outcome;
- a "proved satisfied" disposition requires an exact admitted assurance
  revision for that precondition;
- runtime enforcement, assumption, and deployment-requirement dispositions
  require a retained valid derived realization obligation with exact introducer
  identity;
- there is no native-target-behavior escape hatch.

The consequence space covers UB, poison, unreachable, traps, exceptional halts,
typed realization-capacity exhaustion, and explicitly named other partiality.

## Certified predecessor composition

This proof imports and composes:

- `PHIL-SYS-REALIZE-001` target-strengthening closure, including exact
  strengthening coverage and retained derived realization obligations;
- `PHIL-MEM-FAIL-001`, preserving the already-Certified rule that potentially
  failing physical allocation must have an explicit source/evidence/assumption/
  deployment disposition; and
- `PHIL-VERIFY-ARTIFACT-001` as an independent final-artifact closure layer.

Final artifact certification therefore does not excuse an unresolved runtime
partiality relation. Both layers must close.

## Production authority retained

Concrete production authority remains
`Phil.Systems.RuntimePartialityRelation`, layered over
`Phil.Systems.TargetStrengthening`.

The checker:

- verifies the complete target-strengthening stage first;
- rejects classified preconditions absent from that stage;
- rejects empty/invalid hazard identities;
- constructs the exact expected hazard-pair domain and requires exact equality
  with the disposition domain;
- validates source-outcome, assurance-revision, enforcement, assumption, and
  deployment identities; and
- requires a retained derived obligation for runtime/assumption/deployment
  dispositions.

## Explicit boundaries / TCB

Still explicit:

- concrete target capacity taxonomies and profile-specific capacity facts;
- truth of source assurance revisions and assumptions;
- correctness of accepted runtime enforcement;
- applicability of deployment requirements;
- concrete Text/Map/Set representation and finite enumeration;
- target/backend/toolchain behavior;
- GHC/runtime correctness; and
- Rocq/toolchain correctness.

This proof does not claim those facts are true merely because they are named; it
certifies that the realization cannot omit, merge, or silently reinterpret the
required evidence/disposition structure.
