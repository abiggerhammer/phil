# Phase 1 protocol message admissibility implementation refinement v1

`PHIL-PROT-MSG-001` is already **Discharged / Certified** by `proof/Phil/Core/ProtocolMessageAdmissibility.v`.

This staging slice extracts only the protocol-specific admission decisions that production currently makes after concrete Haskell traversal has established the relevant facts.

## Extracted decision surface

`ProtocolMessageAdmissibilityKernel` owns the fail-closed contract decision in existing production precedence:

1. contract revision is nonempty;
2. contract type exactly matches the actual type;
3. contract semantic identity exactly matches the actual semantic form;
4. recursive semantic shape is admissible;
5. recursive hard Core type is admissible.

It also owns the final yes/no decision for the intrinsic concrete-message subset after native recursive type traversal has supplied the corresponding fact.

The extracted layer does not carry Haskell diagnostic paths/details. Rejection constructors identify only the semantic reason class so production can retain its richer native diagnostics.

## Explicit native and predecessor boundaries

The following remain outside the extracted kernel:

- concrete `Ty`, `SemanticForm`, and `Text` representation/equality;
- recursive list/product/refinement traversal;
- discovery and preservation of exact aggregate index paths;
- construction of `BoundaryMessageInadmissibility` diagnostics and details;
- generic argument normalization and protocol-family orchestration;
- generic discharge, template substitution, and session duality;
- ownership/resource transfer and exactly-once authority;
- rendezvous, Session action, target serialization, ABI/wire/runtime behavior;
- GHC, Rocq extraction, and runtime correctness.

In particular, Message admission cannot manufacture ownership-transfer authority. Transfer remains downstream and independent, exactly as in the Certified theorem.

## Staging rule

Production `src/Phil/Core/Protocol/MessageAdmissibility.hs` remains unchanged in this PR.

The Phase 1 Protocol Message Admissibility workflow recompiles the Certified theorem and implementation correspondence, fresh-extracts the kernel, strict-typechecks and executes direct controls, strict-typechecks unchanged production paths, and reruns the existing Message/projection/restricted-transfer corpora.

A green staging run therefore leaves `PHIL-PROT-MSG-001` at **Discharged / Certified** pending a separate production-binding closeout.
