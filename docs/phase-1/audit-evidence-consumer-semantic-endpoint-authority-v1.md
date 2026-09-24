# Phase 1 audit: semantic endpoint authority for evidence occurrences

This defensive proof-correspondence slice continues D-RES-SUPPORT-01 / D-RES-TREE-01 after exact actual-use, subject-occurrence, same-event final-use, and approved event-origin correspondence.

The existing chain establishes that every represented actual subject occurrence has source and target `SubjectId` endpoints, legal `ExportSubject` transport, and an exact original event with approved producer origin. That still does not establish that the endpoint pair came from competent semantic evidence. Numerically matching endpoint metadata, a reused source name, or a compatible type must not become proof authority by itself.

`EvidenceConsumerSemanticEndpointAuthority.v` therefore adds one explicit boundary:

- every actual subject-bearing occurrence keeps its exact source and target endpoints;
- the occurrence is qualified under the same exact original event already used by the event-origin proof;
- that exact event/occurrence/source/target tuple must have competent semantic endpoint authority;
- authority attached to a different event is insufficient;
- complete multi-subject occurrence correspondence remains valid when each exact endpoint pair is competently qualified; and
- checked closed uses still require no fabricated subject endpoint.

## Native correspondence boundary

The proof intentionally does not manufacture the competent relation. The production implementation must reflect it from actual declaration, binding, or checked-rebase evidence associated with the approved original result/event. A local `(use index, occurrence index)` identifies a position inside one authentic returned result; it is not by itself a global semantic `SubjectId` or historical event identity.

The proof also does not infer authority from source spelling, source position, a matching type, `ResidualSpec` presence, or later metadata reconstruction. Logical subject survival remains separate from one-use resource permission, and consumed affine/linear ownership is not restored.

## Acceptance cases

1. Complete event-origin correspondence with unqualified endpoint metadata is insufficient.
2. Endpoint authority for a different event is insufficient.
3. A two-subject use with both exact endpoint pairs competently qualified under its approved event succeeds.
4. A checked closed use succeeds without invented endpoint authority because it has no actual subject occurrence.

This slice changes only a Rocq proof module, this note, and an isolated proof workflow. It does not modify production Haskell, source admission, ownership/loan semantics, native lowering, packaging, or any Phase 1 trusted-computing-base boundary. LLVM remains trusted in Phase 1.
