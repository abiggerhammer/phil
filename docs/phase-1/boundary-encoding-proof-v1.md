# Phase 1 Boundary Encoding Proof v1

## Obligation

`PHIL-BND-ENCODE-001` certifies the bounded semantic contract implemented by BND-008–010.

This proof is about **what evidence is sufficient to treat an output as a checked boundary encoding**, not about the correctness of any concrete byte encoder or transport.

## Certified semantic scope

The Rocq model in `proof/Phil/Core/BoundaryEncoding.v` establishes:

- generated encoding evidence is available only from an admitted encoder;
- successful evidence is tied to the exact encoder implementation, boundary representation revision, and output subject;
- a representation mismatch or output-subject mismatch rejects explicitly;
- ordinary valid encoding does not imply canonical encoding;
- canonicality is enforced only when the boundary contract explicitly requires it;
- a declared canonical encoding rejects a legal-but-noncanonical grammar member while preserving the exact representation/output subject in the rejection;
- checked serialization requires an exact representation and exact subject;
- raw host-memory layout is never sufficient serialization correspondence;
- matching C-struct shape is never sufficient serialization correspondence; and
- every successful checked-wire correspondence necessarily has checked-wire basis plus exact representation and subject identity.

The provider/qualification fact that an encoder is admitted is imported as a checked fact. This theorem does not infer provider competence from implementation identity.

## Correspondence evidence

The dedicated `Phase 1 Boundary Encoding Proofs` workflow:

1. compiles the Rocq theorem under Rocq 9.2.0;
2. records exact source and `.vo` SHA-256 identities;
3. typechecks the unchanged production modules:
   - `src/Phil/Core/QualifiedEncoding.hs`
   - `src/Phil/Core/EncodingCanonicality.hs`
   - `src/Phil/Core/BoundarySerialization.hs`
4. typechecks and reruns the unchanged BND-008–010 tests:
   - `test/Phase1QualifiedEncodingMain.hs` — 4 cases;
   - `test/Phase1EncodingCanonicalityMain.hs` — 3 cases;
   - `test/Phase1BoundarySerializationMain.hs` — 5 cases.

Total focused correspondence corpus: **12 cases**.

## Residual boundary

This is semantic certification, not implementation refinement.

Explicit residual boundaries include:

- Rocq kernel/toolchain correctness;
- concrete Haskell `Name`, `BoundaryRepresentationId`, and equality representation;
- truth/competence of provider or qualification evidence that admits an encoder;
- concrete encoder implementation correctness;
- exact emitted bytes and wire-I/O behavior;
- grammar implementation correspondence;
- Haskell error reconstruction and ordering;
- Haskell implementation equivalence;
- target ABI/layout facts and zero-copy realization.

A future claim that a particular encoder emits the correct bytes for a wire format must supply its own provider/target evidence or stronger mechanical refinement.

## Dependencies

- `PHIL-BND-REP-001`
- `PHIL-PROV-QUAL-001`
- ADR-023

Baseline: merged #403, `1dbd352192997cd102836bf0436a67e311449b60`.
