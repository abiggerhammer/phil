# PHIL-PROT-ID-001 production binding v1

This closeout binds the already-Certified protocol identity semantics to the exact Rocq-extracted decision kernel staged in #442.

## Exact kernel

Production checks in `src/ProtocolIdentityKernel.hs` byte-for-byte from the successful #442 extraction.

SHA-256:

`2e26ec8b481ca72b0813285da1b7f7d91f68b875584065a63955dc17c671ba8d`

The closeout workflow fresh-extracts the kernel and rejects any byte or SHA mismatch before running production correspondence tests.

## Bound production choices

`src/Phil/Core/Protocol.hs` keeps its public Haskell API, concrete `Text`, `Name`, `Session`, `Map`, rich diagnostics, resource-context checks, Session execution, and metadata progression.

The extracted kernel now owns these semantic choices:

1. endpoint contract correspondence rejects in exact order: protocol instance, role, then local Session;
2. protocol action identity rejects in exact order: protocol instance, then role;
3. after native resource agreement, the native Session checker result is reflected back through the extracted action decision as current-local-state admission/rejection; and
4. `protocolEndpointContract` reconstructs the exact instance/role/session coordinates through the extracted `planProtocolContract` constructor.

The action gate is deliberately applied in two stages. This preserves the existing native precedence in which instance/role identity rejects before resource-context agreement, while Session-action admission is checked only after resource agreement. The exact staged kernel makes the held-true coordinates in each partial application mechanically fixed.

## Still native or predecessor-owned

This refinement does not claim to prove:

- concrete Haskell equality for `Text`, `Name`, or `Session`;
- endpoint-map lookup or map-key integrity;
- resource-context agreement;
- correctness of the Session transition implementation;
- exact predecessor removal / successor installation, owned by the progression/session obligations;
- occurrence provenance;
- transport or runtime realization identity;
- target serialization, ABI, or wire behavior; or
- GHC, Rocq extraction, runner, or runtime correctness.

Occurrence names, transport identity, and runtime representation remain absent from the extracted identity decision surface, matching the Certified noncollapse theorem.

## Closeout criterion

`PHIL-PROT-ID-001` may move from `Discharged / Certified` to `Discharged / Implementation Refined` only after an exact-head run:

- recompiles the Certified theorem and implementation correspondence;
- fresh-extracts `ProtocolIdentityKernel.hs`;
- byte-compares it to the checked-in production kernel and asserts the staged SHA;
- strict-typechecks the checked-in kernel and bound `Protocol.hs`;
- reruns the direct extracted-kernel controls against the checked-in kernel;
- reruns the unchanged PROT-001, PROT-002, and SYS-009 pressure corpora; and
- emits production-binding artifact identities.
