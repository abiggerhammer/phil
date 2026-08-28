# Phase 1 protocol progression / guard proof

This note records the Rocq certification target for `PHIL-PROT-STEP-001`, covering the already implemented/tested PROT-005 and PROT-006 slices.

The proof deliberately composes existing certified boundaries instead of inventing a second session or assurance model:

- `PHIL-PROT-ID-001` remains authoritative for exact protocol instance, role, and current local-session action identity;
- `PHIL-SESSION-STEP-001` remains authoritative for linear resource consumption and successor installation at the Core session layer; and
- `PHIL-DISCH-BOUNDARY-001` / the assurance verifier remain authoritative for whether exact obligation revisions have competent accepted evidence.

## Protocol occurrence progression

`proof/Phil/Core/ProtocolProgressionGuard.v` models the Phase 1 protocol metadata map separately from the already-certified linear resource theorem.

A successful continuing transition:

- requires a live predecessor occurrence;
- requires a distinct, unoccupied successor occurrence;
- removes the predecessor occurrence;
- installs exactly one successor carrying the predecessor's exact protocol instance and role plus the successor `Session` supplied by the session calculus; and
- preserves every unrelated occurrence.

The consumed predecessor is therefore stale immediately after success. Any second continuation attempt addressed to that predecessor rejects regardless of whether the successor session has the same syntactic communication shape. Same-name successor reuse and occupied-successor collisions reject.

A successful close removes the predecessor and installs no successor; repeating close on that consumed occurrence rejects.

## Exact guard authority

The guard theorem keeps assurance truth abstract through two exact-revision predicates: the required obligation revision must be present and certified by the assurance layer.

A guarded action is allowed only when:

- guard requirements contain no duplicates;
- every exact required guard revision is present and certified; and
- the ordinary Core `ProtocolActionAllowed` relation holds.

Consequences proved directly include:

- structural action availability / a branch label does not supply missing guard authority;
- authority for another guard revision cannot substitute for the required revision;
- protocol-declared and architecture-strengthening guards compose conjunctively;
- duplicate guard requirements reject;
- guard evidence cannot legalize a structurally illegal Core action; and
- guarded actions still require exact protocol instance, role, and current-local-session admission from `PHIL-PROT-ID-001`.

## Correspondence pressure corpus

The dedicated workflow reruns the unchanged implementation tests:

- `test/Phase1ProtocolStaleEndpointMain.hs` — 7 PROT-005 cases;
- `test/Phase1ProtocolGuardedTransitionMain.hs` — 9 PROT-006 cases.

It also typechecks the unchanged `Phil.Core.Protocol` and `Phil.Assurance.ProtocolGuard` paths under the repository warning discipline.

## Residual boundary

This certification is a normalized semantic proof, not an implementation-refinement claim. Concrete `Map`/`Text`/`Session` representation, the exact correspondence between protocol metadata removal and the separately certified resource-context update, assurance-ledger/manifest enumeration, evidence producer truth, diagnostics, and Haskell implementation equivalence remain explicit later refinement or trusted correspondence boundaries.
