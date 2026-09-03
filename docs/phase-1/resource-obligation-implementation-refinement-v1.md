# PHIL-RES-OBL-001 implementation refinement v1

This slice stages machine implementation refinement for the already-Certified obligation non-laundering theorem without changing production Haskell.

## Extracted decision

`decidePendingObligationReconvergenceByFacts pendingBefore pendingAfter` accepts exactly when reconvergence does not lose an unresolved obligation:

- if `pendingBefore` is true, `pendingAfter` must also be true;
- if `pendingBefore` is false, this theorem imposes no obligation-disposition requirement on reconvergence.

The extracted decision therefore models the Certified implication

`PendingObligation before -> PendingObligation after`.

This is intentionally narrower than inventing a concrete five-way disposition ledger. The current Haskell checker stores unresolved obligations in `residualObligations`; discharge, runtime binding, permitted assumption, and permitted export are owned by their existing semantic boundary/evidence rules. The Certified theorem proves that an obligation still observed as pending after reconvergence cannot simultaneously have one of those explicit dispositions.

## Composition

The theorem composes the existing Certified `ProcessJoin` payload-preservation result. `joinBranches` may normalize the `ResourceContext` of a continuing path, but reconvergence itself does not own obligation disposition.

Repeated reconvergence is ordinary composition of the same pending-preservation decision, matching the Certified repeated-reconvergence theorem.

## Direct controls

The staging harness executes the complete four-case Boolean truth table:

1. pending -> pending: accept;
2. pending -> absent: reject as lost;
3. absent -> pending: accept (no unresolved input was lost);
4. absent -> absent: accept.

The unchanged two-case RES-011 corpus is rerun after the extracted controls.

## Boundaries

Production remains unchanged in this staging slice. A later production-binding closeout must derive both Boolean facts from the actual per-path `residualObligations` maps around continuing-path normalization. It must not pass a hard-coded postcondition or fabricate a discharge/runtime-binding/assumption/export status.

Exact diagnostics, obligation creation/discharge semantics, runtime evidence truth, permitted assumption/export policy, ProcessJoin resource normalization, and backend/runtime correctness remain at their existing owners.
