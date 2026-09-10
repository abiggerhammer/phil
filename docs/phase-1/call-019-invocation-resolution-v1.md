# CALL-019 — ordinary component/callable invocation resolution

Status: first implementation slice for `PHIL-CALL-INVOKE-001` / `CALL-019`.

This slice establishes the exact source-resolution substrate required before the concrete `invoke` expression is connected to callable execution.

An ordinary named callable lookup is not provider-primitive lookup. Display spelling is only a lookup handle. Successful resolution returns the exact persisted `DeclarationKey` together with the selected callable semantic surface; a provider primitive with the same display spelling does not create ambiguity because it belongs to a different competence path.

The resolution boundary fails closed for:

- unknown callable spelling;
- multiple callable declarations with the same visible spelling;
- a provider-only spelling presented as a callable;
- stale or mismatched declaration identity;
- stale or mismatched callable interface revision; and
- a callable whose semantic surface does not refine the expected callable contract.

A callable and a provider primitive may intentionally share spelling. The future explicit `invoke Callee(args)` source form selects this callable-resolution path; ordinary provider-operation expressions remain on the provider-primitive path. No implementation-selected namespace precedence is admitted.

This slice does not yet claim source syntax, argument/resource transfer, callee lifecycle execution, or Steve composition. Those remain the next CALL-019 slices and must reuse the existing callable checking/refinement/lifecycle machinery rather than introducing a second invocation semantics.
