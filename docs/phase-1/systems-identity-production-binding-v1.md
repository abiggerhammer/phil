# PHIL-SYS-ID-001 production binding

This closes machine implementation refinement for already-Certified `PHIL-SYS-ID-001` after staging PR #559.

## Exact staged kernel

- staging PR: #559
- staging exact green head: `5d353adabbdc0189f29cb3df2491d1181a2e6bf5`
- staging merge: `13a1bf1356b7894358de57acafd89e8ceeb0f539`
- exact `SystemsIdentityKernel.hs` SHA-256: `90a5a62df64ec43939379149b24a0f2dd8fd3afd1625eb4ab03598e9ddbc1a53`
- checked-in raw copy: `generated/SystemsIdentityKernel.hs`
- production mirror: `src/SystemsIdentityKernel.hs`

Both checked-in copies preserve the exact staged extraction bytes, including the two trailing newlines.

## Production ownership

`Phil.Systems.Verify` retains all concrete work and existing typed diagnostic ordering:

- construction and comparison of concrete `Digest` values;
- canonical Systems-program, Systems-artifact, lowering-decision, and lowering-root recomputation;
- assurance-manifest lookup and validation;
- `Map`/`Set`/list traversal and decision enumeration;
- all non-identity Systems semantic, evidence, cost, runtime, and StageContract checks.

After the native artifact-identity and lowering-ledger checks succeed, production recomputes the ten normalized facts certified by `proof/Phil/Systems/Identity.v` and requires the exact extracted kernel to agree:

1. five artifact-identity equality gates through `decideArtifactIdentityByFacts`; and
2. five per-decision binding gates through `decideDecisionBindingByFacts` for every lowering decision.

Impossible disagreement after native verification fails closed through a certified-kernel invariant. Native rejection payloads and ordering are unchanged.

## Deliberate boundary

The theorem and extracted kernel treat digests as opaque identities. Concrete serialization, SHA-256 collision resistance/injectivity, digest-construction correctness, assurance-manifest construction, container correspondence, external evidence truth, runtime/backend behavior, and Rocq/GHC correctness remain explicit representation/evidence/TCB boundaries.

## Closeout gate

The dedicated `Phase 1 Systems Identity Production Binding` workflow:

- recompiles `PHIL-SYS-ID-001` and its implementation-correspondence theorem under Rocq 9.2.0;
- fresh-extracts `SystemsIdentityKernel.hs` and requires SHA-256 `90a5a62df64ec43939379149b24a0f2dd8fd3afd1625eb4ab03598e9ddbc1a53`;
- byte-compares fresh extraction against both checked-in copies;
- strict-typechecks the exact production kernel and bound `Phil.Systems.Verify` path;
- executes the same **12 direct controls** through the production mirror; and
- reruns the unchanged **20-case** `phil-systems-tests` corpus through `verifySystemsArtifact`.

A fully green exact head permits promotion of `PHIL-SYS-ID-001` to `Discharged / Implementation Refined`. At that point every Certified Systems/StageContract aggregate in ledger rows 67–75 is machine Implementation Refined.
