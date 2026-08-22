# Phil

**Phil** is a systems language in which architecture is executable and implementation is replaceable.

It is part of the broader Logics to Order research program. Phil starts from system boundaries, protocols, authority, and proof obligations, then makes those architectural facts executable and checkable rather than treating a particular implementation as the definition of the system.

## Core formulations

**What Phil is**

> **Phil is a systems language in which architecture is executable and implementation is replaceable.**

**How Phil works**

> **Phil constructs software top-down from boundaries, protocols, and obligations.**

**How Phil is used**

> **Prototype → verify → rewrite → certify.**

**Assurance cost**

> **Phil makes the cost of assurance explicit and erases assurance machinery that has completed its work.**

> **Proof should cost at compile time; uncertainty should cost at runtime.**

## Repository status

This repository currently contains the executable Phase 0 Phil Core checker, the accepted upload witnesses, the rejected conformance corpus, the Rocq proof corpus, and the first trusted Phil source front end.

The source front end parses the Phase 0 witness language with source locations and full-input consumption, then canonically elaborates the refinement/type/value subset whose Core meaning is already executable. Whole-component semantic checking of parsed source is the next slice.

To exercise the parser directly:

```text
cabal run phil-core -- parse examples/upload/client.phil
```

A successful `parse` command means only that the file is syntactically valid Phil. It deliberately does **not** claim semantic acceptance.

## Current implementation layers

The checker currently has executable support for:

- unrestricted, affine, and linear resource contexts;
- scoped shared loans;
- binary session progression and guarded recursion;
- path-sensitive process/control checking;
- recognition-gated grammar-backed receives;
- bidirectional value checking;
- restricted refinements, evidence, explicit transport, and sort checking;
- deterministic focusing and claim elaboration;
- certificate-checked transparent decision procedures;
- named obligation disposition at required points;
- a location-preserving Phase 0 surface parser and deterministic fragment elaborator.

See `docs/implementation-status.md` for the exact implemented/non-goal boundary. The Drive design package remains normative for accepted Phase 0 semantics; repository code and proofs are the executable evidence against that design.
