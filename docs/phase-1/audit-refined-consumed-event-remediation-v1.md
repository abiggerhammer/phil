# PHIL-AUD refined consumed-event interpretation remediation v1

This implementation-side remediation follows the independent Phase 1 audit handoff `PHIL-AUDIT-20260924-REFINED-EVENT-MODES-IDENTITY`.

The failing case is an actual refined value checked in affine or linear mode, then consumed while a residual obligation remains. The returned checker state correctly has no resource owner, but it retains the exact logical subject typing captured with that residual. The ordinary resolver can still interpret the residual under the explicitly supplied runtime policy. The original-event adapter previously inserted the target refinement's plain base as a fallback subject type and then rejected the retained refined type as a conflict.

The repair keeps ownership and logical interpretation separate. After validating the exact returned residual records, `resolveOriginalCheckEvent` first merges their retained logical subject bindings. If the checked structural owner is still live, its exact same-mode type remains authoritative as before. If the owner is gone, the adapter may reuse the exact retained logical type for that subject only when that type is the checked base or a refinement chain whose erasure reaches the checked base. If no retained interpretation exists, the prior plain-base fallback remains. Incompatible retained types still fail closed.

This does **not** restore an affine or linear resource, manufacture unrestricted evidence, accept unrelated same-named refinements, weaken residual metadata checks, or use the target refinement predicate as proof of itself. Runtime discharge remains the explicit responsibility of the supplied `DischargePolicy`.

`Phase1AuditRefinedConsumedEventMain.hs` permanently replays six requirements from the independent handoff: four controls establish genuine linear/affine consumption, exact retained refined support, and ordinary resolver success; two requirements verify that the original-event adapter now produces the same legitimate runtime disposition while all resource maps still exclude the consumed owner.

Residual-free original-event provenance remains a separate correspondence problem. This slice does not claim to recover occurrence metadata for successful checks that return no residual identity.
