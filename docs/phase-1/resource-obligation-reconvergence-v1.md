# RES-011 — obligation reconvergence

Phase 1 does not permit an unresolved obligation to disappear merely because control-flow reconverges.

The Core process model already preserves this property by keeping residual obligations inside each continuing `CheckState`. `joinBranches` normalizes the continuing resource contexts, but it does not replace, union, or erase the per-path `residualObligations` maps. A branch-specific unresolved obligation therefore remains represented on that continuing path after a join.

The same rule applies to repeated reconvergence, including loop-like re-entry: carrying a continuing path through another join does not discharge or erase its unresolved obligation.

RES-011 therefore closes as a conformance property of the existing path-sensitive process model. Discharge, runtime binding, permitted assumed/exported boundaries, and other explicit dispositions remain separate semantic events; reconvergence itself is not one.

The dedicated corpus in `test/Phase1ObligationReconvergenceMain.hs` checks both first reconvergence and repeated reconvergence under `-Wall -Werror`.
