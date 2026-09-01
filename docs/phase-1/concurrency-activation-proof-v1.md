# Phase 1 concurrency activation proof boundary v1

`PHIL-CONC-ACTIVATE-001` certifies the process activation / participant / initial ownership partition immediately above the already Certified `PHIL-CONC-SEM-001` bounded concurrency semantics.

The Rocq model proves that:

- the exact static process population and activation map satisfy the certified concurrency population invariant;
- every initial activation binding is explicit architecture-owned input, never ambient state;
- every binding names an already activated process;
- restricted initial ownership is exact and functional, with no manufactured owner entries;
- direct reachable stateful semantic occurrences are functional across process contexts, so unrestricted structural wrappers cannot authorize a second direct owner;
- every expected protocol role has an explicit participant classification;
- every internal participant names both an activated ProcessKey and a member of the static process population;
- external classification carries no ProcessKey and cannot itself manufacture an internal activation.

The proof does **not** claim that external classification selects or discharges entry, transport, BoundaryRepresentation, authority, assumption, export, or realization relations. Those remain separate explicit contracts.

The concrete Haskell representation and extraction boundary remains checked by correspondence: `ProcessActivation.hs`, `ProcessParticipants.hs`, and the unchanged CONC-001/002/003/010/011 conformance corpus are strict-checked/rerun alongside the Rocq proof.

ProcessKey persistence/serialization, parser-to-architecture occurrence correspondence, provider qualification implementation, and concrete unrestricted-wrapper reachability traversal remain representation/tooling boundaries rather than proof-side identities.
