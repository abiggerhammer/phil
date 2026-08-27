# Provider state implementation refinement v1

`PHIL-PROV-STATE-IMPL-001` mechanically connects the bounded PROV-006 provider-state checker to the Certified `PHIL-PROV-STATE-001` semantics.

The extracted kernel owns the finite traversal shape for:

- exact visible-initial-state domain correspondence;
- admissible abstract initial-state membership;
- membership of each initial implementation/abstract pair in the named relation;
- exact qualified provider-operation lookup;
- exact implementation-outcome to public-outcome lookup;
- rejection when a reachable implementation transition starts with no related abstract pre-state; and
- universal simulation checking for every related abstract pre-state against the supplied public transition relation and successor-state relation.

The exact generated `ProviderStateQualificationKernel.hs` is checked into `src/` and must regenerate byte-identically from Rocq. The production `checkProviderStateSimulation` path projects the already-qualified provider semantics and PROV-006 `Map`/`Set` state model into canonical finite lists and delegates acceptance to `decideProviderStateSimulation`.

Before the kernel result is trusted, every production `Map`/`Set` participating in the projection must round-trip through `toAscList`/`fromAscList`. The handwritten traversal remains only for stable diagnostics and construction of `CheckedProviderStateQualification`. If the extracted kernel and diagnostic reconstruction disagree in either direction, production fails closed with `ProviderStateQualificationRepresentationMismatch`.

The production projection contains:

- visible implementation initial states as ascending set order;
- admissible abstract initial states as ascending set order;
- the exact initial implementation-to-abstract map as ascending map order;
- the already-checked PROV-001--005 operation/outcome correspondence as nested ascending maps;
- named implementation/abstract relation pairs as ascending set order;
- reachable implementation transitions as ascending set order; and
- allowed public contract transitions as ascending set order.

This is an asymmetric simulation check: an implementation may realize fewer public transitions, but every supplied reachable implementation transition must use a qualified operation/outcome, start inside the named relation, simulate an allowed public transition for every related abstract pre-state, and finish in a related abstract successor state.

The kernel deliberately treats the supplied reachable implementation transitions, state relation, public transition relation, and admissible-initial set as qualification facts. It does not infer that those finite facts exhaust real runtime behavior. Reachability/completeness, crash/interference truth, backend correctness, Rocq extraction/toolchain correctness, GHC/runtime behavior, concrete key equality, and `Map`/`Set` semantics remain explicit evidence or TCB boundaries.

The staging extraction landed in #243 from exact green head `5c2a2dac64c2121a404e96dbedfa27762b982a89`; artifact `9633147268` had digest `sha256:61c77010ed7c14ef1b47068bdd0bdaecce5e9e763c4cd9ace8582a8564b12039`. The harvested generated kernel is 10,819 bytes with SHA-256 `34d66127bdd9ef8e7120b711cad4029bdbf9b0f654954f263ef95dad4fae6012`.

PROV-007 provider-wide history laws and PROV-008 lifecycle/interruption behavior remain separate production-refinement slices after PROV-006.
