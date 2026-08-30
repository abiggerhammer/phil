# PHIL-BND-ENCODE-001 production binding

This closeout binds the production BND-008–010 decision surface to the exact Rocq-extracted implementation kernel staged by #427.

## Exact extracted kernel

`src/BoundaryEncodingKernel.hs` is checked in byte-for-byte from the #427 proof artifact.

SHA-256:

`3f578c37a2636a83458f9dd3ba44621131468a23fa5d3fb7a418735c0677238d`

The production-binding workflow fresh-extracts the kernel from `BoundaryEncodingImplementationExtraction.v`, byte-compares the result with the checked-in file, and rejects any digest other than the value above.

## Qualified encoding binding

`Phil.Core.QualifiedEncoding` continues to own the native Haskell types, concrete identity/equality facts, provider-admission reflection, detailed error reconstruction, and public `GeneratedEncodingEvidence` value.

The branch decision is now delegated to `decideQualifiedEncodingByFacts` in the extracted kernel in the Certified order:

1. encoder admitted;
2. exact boundary representation;
3. exact output owner.

On acceptance, the three generated-evidence coordinates are routed through `planGeneratedEncoding` before native reconstruction:

- encoder implementation;
- representation revision;
- output owner.

The truth of provider admission and the correctness of the concrete encoder remain outside this kernel.

## Canonicality binding

`Phil.Core.EncodingCanonicality` translates its public requirement/form enums to their extracted counterparts and delegates the semantic decision to `decideEncodingCanonicality`.

The public behavior remains exactly bounded:

- no canonicality declaration does not reject a legal noncanonical grammar member;
- declared canonicality accepts a canonical grammar member; and
- declared canonicality rejects a legal noncanonical member.

Concrete classification of an emitted encoding as canonical or noncanonical remains a native/external fact.

## Serialization binding

`Phil.Core.BoundarySerialization` translates the public serialization-basis enum and reflects exact representation/subject equality into the extracted `decideBoundarySerializationByFacts` decision.

The Certified order remains:

1. reject raw-memory layout as correspondence evidence;
2. reject matching C-struct shape as correspondence evidence;
3. for checked-wire correspondence, require the exact representation;
4. then require the exact subject.

The existing public errors preserve concrete expected/actual identities. Actual byte emission, wire I/O, ABI/layout claims, and zero-copy realization remain separate boundaries.

## What this closes

A green exact-head closeout establishes the bounded implementation correspondence for the semantic choices proved by `PHIL-BND-ENCODE-001`: qualified admission/identity gating, exact evidence construction, opt-in canonicality, and checked-wire serialization gating.

It does not certify concrete encoder correctness, byte-level wire behavior, parser/grammar implementation equivalence, ABI/layout correspondence, or zero-copy realization.

After the closeout lands, the logic ledger may move `PHIL-BND-ENCODE-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
