# Protocol progression / guard implementation refinement v1

This note stages mechanical implementation refinement for Certified `PHIL-PROT-STEP-001` without changing production behavior.

The Certified theorem composes already-owned protocol identity and Session progression with the protocol metadata and assurance-guard layers. The extracted implementation seam therefore does **not** reimplement session legality, resource mutation, protocol instance/role checks, or evidence truth.

## Extracted decision surface

`ProtocolProgressionGuardImplementation.v` extracts five small representation-neutral operations:

- continuation classification from reflected predecessor-liveness, successor-distinctness, and successor-freshness facts;
- close classification from reflected predecessor-liveness;
- exact successor instance/role/session reconstruction;
- duplicate-vs-unique guard-list classification; and
- exact guard-revision admission from reflected present/certified facts.

The continuation decision preserves the Certified rejection precedence: missing/stale predecessor first, same-name successor second, occupied successor third, then acceptance. The guard requirement decision preserves missing revision before present-but-uncertified.

## Explicit native / predecessor boundaries

Production remains unchanged in this staging PR.

The following stay explicit boundaries:

- `ProtocolIdentityKernel` remains the production authority for exact protocol instance/role/current-local-state action gating;
- the Session checker remains the authority for action legality, endpoint resource consumption, and exact successor Session;
- concrete `Map`/`Set`/`Text`/`Name`/`Session` representation and equality remain native;
- protocol endpoint-map lookup, deletion/insertion, and exact diagnostics remain native;
- `verifyManifest` remains the authority for evidence truth, acceptance rules, validity scope, and assurance-graph correctness;
- concrete guard-list traversal and exact duplicate diagnostic payloads remain native; and
- resource-context / protocol-metadata correspondence remains compositional rather than replaced by a monolithic checker.

## Staging correspondence

The dedicated workflow recompiles the Certified theorem and this implementation correspondence, fresh-extracts `ProtocolProgressionGuardKernel.hs`, strict-typechecks and runs direct decision controls, strict-typechecks the unchanged production protocol and guard paths, and reruns the unchanged PROT-005 / PROT-006 pressure corpora.

A green staging run leaves `PHIL-PROT-STEP-001` at `Discharged / Certified`. A separate closeout must check in the exact extracted kernel and bind the production metadata/guard choices before the ledger may be promoted to `Implementation Refined`.
