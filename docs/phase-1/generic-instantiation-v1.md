# Phase 1 generic instantiation v1

This tranche begins logic-ledger obligation `PHIL-GEN-INST-001` and conformance cases `GEN-007`, `GEN-008`, and `GEN-012`.

The checked public requirement vocabulary now includes exact structural permissions, provider interface revisions, and propositions. Instantiation supplies one explicit disposition for every exact public requirement and rejects missing, duplicate, or unrelated dispositions.

Provider requirements are satisfied only by the exact required `InterfaceRevision` or an already checked provider refinement/projection whose target is that exact revision. A merely richer nominal operation set is not provider satisfaction. Proving the provider refinement itself remains an ADR-021 / provider-qualification responsibility.

Provider availability and provider-law evidence are separate. Closing an exact provider contract requirement does not close a proposition/law requirement; proposition evidence must name the exact required proposition in this bounded checker.

An unmet requirement never becomes an assumption implicitly. Assumption-dependent or exported dispositions are explicit records and are admissible only when the enclosing `GenericInstantiationPolicy` permits them. The strict policy permits neither.

The stabilized structural requirements from the preceding tranche lift directly into the same exact requirement/disposition checker, so structural instantiation is not a parallel mechanism.

This slice does **not** yet claim the Rocq proof for `PHIL-GEN-INST-001`, ADR-021 provider qualification, callable/static-contract requirements, full proposition subject/context validity, runtime/deployment dispositions, generic semantic application identity (`PHIL-GEN-ID-001`), conditional assurance reuse, final source syntax, or lowering.
