# Provider lifecycle implementation refinement v1

`PHIL-PROV-LIFECYCLE-IMPL-001` mechanically connects the bounded PROV-008 lifecycle/interruption checker to the Certified `PHIL-PROV-STATE-001` provider-state/law/lifecycle semantics.

This first tranche is an extraction/staging slice. It does **not** yet change production Haskell acceptance.

The extracted kernel owns the finite traversal shape for:

- exact lifecycle interruption-point domain correspondence between the public contract and implementation model;
- qualification of every lifecycle point's public provider operation;
- exact lookup of the modeled observations for each interruption point;
- universal checking of every modeled interruption observation at the contract's declared public observation boundary;
- independent allowed-set membership for observable state;
- independent allowed-set membership for cleanup/resource residue; and
- independent allowed-set membership for retry disposition.

The normalized extraction model uses tuple projections for lifecycle points, allowances, and interruption observations, plus canonical finite lists for operation keys and allowed sets. The production binding tranche will project the concrete `Map`/`Set` structures into canonical ascending lists, require exact round trips, check in the byte-identical generated kernel, route `checkProviderLifecycleQualification` acceptance through the extracted decision, and retain the handwritten traversal only for diagnostics/result reconstruction.

The theorem establishes the exact executable acceptance structure. It deliberately treats the supplied interruption model as qualification evidence; it does not infer that the finite observation sets exhaust real crash/interruption behavior. Reachability/model completeness, actual crash boundaries, scheduler/environmental interference, backend correctness, Rocq extraction/toolchain correctness, GHC/runtime behavior, concrete key equality, and `Map`/`Set` semantics remain explicit evidence or TCB boundaries.

PROV-008 remains `Mechanized` after this staging tranche and becomes `Implementation Refined` only when the production-binding tranche lands.
