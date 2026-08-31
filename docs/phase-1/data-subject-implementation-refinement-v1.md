# Data subject implementation refinement v1

`PHIL-DATA-SUBJECT-001` is already Certified. This staging tranche extracts only its bounded executable decision surface; production behavior is unchanged.

## Extracted semantic seams

The Rocq implementation correspondence exposes three ordered decisions.

1. **Common update prerequisites** — predecessor consumed, replacement constructed, prior/replacement stable identity, stable-kind agreement, evidence template mentions its subject, exact evidence-to-prior binding, and the evidence subject's inherited stable/kind facts.
2. **Subject/transport mode** — an unchanged semantic subject accepts only without transport; a changed subject requires a transport before exact validation.
3. **Exact transport validation** — accepted disposition, nonempty relation revision, exact evidence reference, exact prior/replacement identities, and exact normalized source/target proposition bindings.

The proof relates the reflected prerequisite and transport facts back to the existing Certified predicates and gives direct constructors for the Certified same-subject and changed-subject cases.

## Explicit native boundary

The following remain native representation/runtime facts:

- `RefTerm`, `Proposition`, `Name`, and `Text` representation and equality;
- decoding a stable-id kind from a concrete `RefTerm`;
- source-to-Core stable-subject elaboration;
- proposition mention analysis, substitution, and normalization;
- exact `Maybe DataSubjectTransport` representation;
- transport truth/competence and accepted disposition provenance;
- detailed diagnostic payload reconstruction; and
- GHC/Rocq extraction/runtime correctness.

The evidence-subject stability/kind facts are redundant native consequences once the exact evidence subject identity equals the already-validated stable prior identity. They remain explicit in the extracted prerequisite decision because the Certified model states them separately; a later production bridge must fail closed if that representation invariant is ever violated.

## Staging rule

A green staging run does **not** upgrade the ledger row. `PHIL-DATA-SUBJECT-001` remains `Discharged / Certified` until a separate closeout checks in the exact extracted kernel and routes the production decisions through it with byte-identity CI.
