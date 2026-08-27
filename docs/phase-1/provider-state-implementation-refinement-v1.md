# Provider state implementation refinement v1

`PHIL-PROV-STATE-IMPL-001` mechanically connects the bounded PROV-006 provider-state checker to the Certified `PHIL-PROV-STATE-001` semantics.

This first tranche is an extraction/staging slice. It does **not** yet change production Haskell acceptance.

The extracted kernel owns the finite traversal shape for:

- exact visible-initial-state domain correspondence;
- admissible abstract initial-state membership;
- membership of each initial implementation/abstract pair in the named relation;
- exact qualified provider-operation lookup;
- exact implementation-outcome to public-outcome lookup;
- rejection when a reachable implementation transition starts with no related abstract pre-state; and
- universal simulation checking for every related abstract pre-state against the supplied public transition relation and successor-state relation.

Production `Map`/`Set` values will be projected to canonical finite lists in the binding tranche. Those projections must round-trip exactly before the extracted decision is trusted; handwritten diagnostics may only fail closed if their reconstruction disagrees with the kernel.

The kernel deliberately treats the supplied reachable implementation transitions, state relation, public transition relation, and admissible-initial set as qualification facts. It does not infer that those finite facts exhaust real runtime behavior. Reachability/completeness, crash/interference truth, backend correctness, Rocq extraction/toolchain correctness, and concrete Haskell representation correspondence remain explicit evidence or TCB boundaries.

PROV-007 provider-wide history laws and PROV-008 lifecycle/interruption behavior remain separate production-refinement slices after PROV-006.
