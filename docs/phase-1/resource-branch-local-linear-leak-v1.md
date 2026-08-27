# Phase 1 branch-local linear leak conformance v1

RES-005 makes reconvergence a resource-accounting boundary rather than a cleanup opportunity.

A linear resource that is live on a continuing predecessor must have an explicit disposition before that predecessor reaches an ordinary join. It may be transferred into the post-state, consumed earlier, or returned earlier, but it cannot simply disappear because another branch did not create the same resource.

## Existing checker relation

`Phil.Systems.ControlStateProjection.checkStateProjection` already checks this boundary rule through exact live-linear coverage:

- each predecessor declares the restricted owners that are live at that edge;
- every live linear owner must occur exactly once in the post-state bindings; and
- an unbound live linear owner produces `StateProjectionUnaccountedLinearOwners`.

This is deliberately a Core/Systems validity check. A later lowering pass must not manufacture cleanup in order to make an invalid predecessor edge appear valid.

## Conformance corpus

`test/Phase1BranchLocalLinearLeakMain.hs` checks two cases:

1. when the branch-local owner has already received a valid earlier disposition and therefore is not live at the join edge, the ordinary join is accepted; and
2. when the branch-local owner is still live on one continuing predecessor but is absent from the post-state bindings, the join is rejected and the diagnostic identifies exactly that owner and predecessor projection.

The fixture uses two ordinary continuing predecessors and one fixed linear post-state slot, so the failure cannot be attributed to terminal-arm handling, loop rules, affine optionality, or subject substitution.

This closes RES-005 at the implementation/conformance level using the existing SYS-008 state-projection checker. It does not yet close RES-006 through RES-011.
