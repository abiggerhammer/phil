# Provider lifecycle implementation refinement v1

`PHIL-PROV-LIFECYCLE-IMPL-001` mechanically connects the bounded PROV-008 lifecycle/interruption checker to the Certified `PHIL-PROV-STATE-001` provider-state/law/lifecycle semantics.

The extracted kernel owns the finite traversal shape for:

- exact lifecycle interruption-point domain correspondence between the public contract and implementation model;
- qualification of every lifecycle point's public provider operation;
- exact lookup of the modeled observations for each interruption point;
- universal checking of every modeled interruption observation at the contract's declared public observation boundary;
- independent allowed-set membership for observable state;
- independent allowed-set membership for cleanup/resource residue; and
- independent allowed-set membership for retry disposition.

The exact generated `ProviderLifecycleQualificationKernel.hs` is checked into `src/` and must regenerate byte-identically from Rocq. The production `checkProviderLifecycleQualification` path projects the already-qualified provider operation domain and PROV-008 `Map`/`Set` lifecycle model into canonical finite lists and delegates acceptance to `decideProviderLifecycleQualification`.

Before the kernel result is trusted, every production `Map`/`Set` participating in the projection must round-trip through `toAscList`/`fromAscList` or `toAscList`/`fromAscList` for sets. Cleanup residues are checked recursively because their borrowed/consumed/returned/successor/produced resource components are themselves sets. The handwritten traversal remains only for stable diagnostics and construction of `CheckedProviderLifecycleQualification`. If the extracted kernel and diagnostic reconstruction disagree in either direction, production fails closed with `ProviderLifecycleQualificationRepresentationMismatch`.

The production projection contains:

- already-qualified public provider operation keys in ascending map-key order;
- lifecycle interruption points as exact `(operation, interruption-point)` tuples;
- allowed observable states as ascending set order;
- allowed cleanup residues as ascending set order;
- allowed retry dispositions as ascending set order; and
- modeled interruption observations as ascending point-map order with each point's observation set in ascending order.

The theorem and production binding deliberately treat the supplied interruption model as qualification evidence; they do not infer that the finite observation sets exhaust real crash/interruption behavior. Reachability/model completeness, actual crash boundaries, scheduler/environmental interference, backend correctness, Rocq extraction/toolchain correctness, GHC/runtime behavior, concrete key equality, and `Map`/`Set` semantics remain explicit evidence or TCB boundaries.

The staging extraction landed in #251 from exact green head `377e2f40441825e1c97ebf3bb11afe8db527163e`; artifact `9634731707` had digest `sha256:a9a6f939faaa3102d9af241c91db71a6adbe15fd0f57926476c7061d4f4e9846`. The harvested generated kernel has SHA-256 `dddbf25c0dcf1b3d4bd7a51482f954d9d53a105ab2fffa2de586ae0e616b780e`.

Once the production-binding tranche lands green, PROV-008 is `Implementation Refined`.
