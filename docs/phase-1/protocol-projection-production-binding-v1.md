# Protocol projection production binding v1

This note closes the bounded implementation-refinement correspondence for
`PHIL-PROT-PROJ-001`.

The staging extraction in #446 produced `ProtocolProjectionKernel.hs` with
SHA-256:

`5c4f9dd27b3b54a4cf596dd6f74b8090bf1442891207a4442a637585e580a556`

The closeout checks that exact extracted file into `src/ProtocolProjectionKernel.hs`
and routes the protocol-specific semantic choices through it.

## Bound production choices

`src/Phil/Core/Protocol/Family.hs` still performs concrete Haskell `Map` lookup
and equality. Those native facts are reflected into the extracted kernel, which
owns:

- whether a requested role is declared for projection;
- whether projection evidence names the exact protocol-instance revision;
- whether projection evidence carries the exact selected local Session; and
- exact instance/role/session construction for accepted projection evidence.

The existing diagnostic precedence is unchanged: instance mismatch is checked
before role lookup, and session mismatch is checked only after successful role
lookup.

`src/Phil/Core/Protocol/Generic.hs` still performs the linear resource move and
fresh-name collision checks. The exact protocol instance, role, and local
Session used to reconstruct successor metadata are supplied through
`planTransferredProtocolContract`; only the occurrence name changes natively.

## Deliberately native or predecessor-owned boundaries

This closeout does not move the following into the extracted kernel:

- concrete `Text`, `Map`, `Session`, and equality implementations;
- generic argument normalization and requirement discharge;
- boundary-message admissibility;
- generic application-identity and protocol-revision derivation;
- protocol-template substitution;
- peer-session dual construction;
- truth/implementation of accepted session constraints;
- linear resource consumption/insertion and destination freshness;
- Session action implementation, runtime transport, serialization, or ABI;
- GHC, Rocq extraction/toolchain, and runtime correctness.

A bare `SessionVar` still acquires no communication authority; that remains
covered by the Certified Session/protocol predecessors and the unchanged
PROT-003 pressure corpus.

## Exact-head closeout check

The Protocol Projection workflow fresh-extracts `ProtocolProjectionKernel.hs`,
byte-compares it with the checked-in production kernel, asserts the staging
SHA-256 above, strict-typechecks the bound production paths, executes the direct
kernel controls against the production kernel, and reruns the unchanged
PROT-003 and PROT-004 pressure corpora.

A green exact-head run permits the ledger row to move from
`Discharged / Certified` to `Discharged / Implementation Refined`.
