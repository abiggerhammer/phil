# PHIL-AUD-CALL-LIFECYCLE-PATH-001 remediation

## Audit identity

- Finding: `PHIL-AUD-CALL-LIFECYCLE-PATH-001`
- Event: `PHIL-AUDIT-20260921-CALLABLE-LIFECYCLE-COMPOSITION`
- Original review snapshot: `bb9d36680b336e98ce4a78583602302a87b4b90e`
- Producer: `Phil.Compiler.CallableSurfaceSemantics`
- Semantic summary: `Phil.Compiler.CallableInvocationSemantics`
- Concrete lifecycle consumer: `Phil.Compiler.CallableInvocationLifecycle`
- Public lifecycle-aware context API:
  `checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle`

This slice repairs implementation-side source-path composition. It does not
promote proof or Certified status.

## Root cause

The ordinary Surface checker is path-sensitive, but the compiler-side callable
collector previously projected every invocation into one flat source-order list.
The lifecycle-aware context then interpreted that may-occurrence list as a single
concrete execution trace.

That allowed a replacement performed in one `decide` arm to make its successor
appear available to a mutually exclusive sibling arm or to a continuation that
is not reachable on every branch. The same flattening made one legitimate
one-shot invocation in each alternative look like two sequential uses.

The local Preserve/Consume/Replace transition checker was not the defect. It
correctly checked each transition on the invented sequential state.

## Repair

The compiler now retains two distinct projections after an accepted Surface
check:

1. the existing **flat invocation list**, unchanged in meaning, for conservative
   may-effect, authority and modeled-failure aggregation; and
2. a **source-path family**, where each member is one feasible ordered sequence
   of invocation occurrences through the source control-flow alternatives.

`decide` and `offer` fork the path family from the same prefix. Ordinary
statement/expression sequencing forms path products. Fallback retains both the
primary-success trace and the primary-then-fallback trace instead of flattening
the fallback unconditionally after primary success.

`SurfaceCallableSemanticSummary` carries the semantic-account version of this
path family beside the existing flat account list.

The concrete lifecycle bridge now:

- retains the exact flat account/binding-domain check;
- requires the union of path identities to equal the flat account domain;
- starts every source path from the same incoming callable resource state;
- applies lifecycle transitions sequentially only within that path;
- rejects if any path uses an unavailable predecessor or otherwise violates the
  existing certified Core lifecycle checks;
- requires all accepted path-final callable states to agree before publishing
  one continuation state; and
- deduplicates repeated source occurrences that appear on multiple expanded
  paths only when their before/after lifecycle witness is exactly identical.

This preserves the existing straight-line lifecycle helper semantics while
preventing sibling branches from lending concrete callable availability to one
another.

## Audit replay

`test/Phase1AuditCallableLifecyclePathMain.hs` drives the real chain:

`parseSurfaceFile`
→ `checkSurfaceComponentWithCallableSemantics`
→ `summarizeSurfaceCallableSemantics`
→ `checkSurfaceCallableInvocationSummaryWithOutcomeBranchesAndLifecycle`
→ `applySurfaceCallableInvocationLifecycles`.

The lifecycle bindings are supplied separately because that remains the public
API contract, but their source spans and declaration keys are taken from the
actual collected source accounts.

The twelve cases correspond to Astra's p01–p12 inventory:

- p01: sequential Advance then Finish remains accepted;
- p02: Advance/Finish in exclusive arms rejects unavailable successor;
- p03: reversing arm listing order yields the same semantic rejection;
- p04: isolated Finish remains rejected;
- p05: one one-shot Once invocation in each exclusive arm is accepted;
- p06: actual sequential double Once remains rejected;
- p07: isolated Advance leaves its successor available;
- p08: preserving Observe in both alternatives remains accepted;
- p09: missing lifecycle binding domain remains rejected;
- p10: repeated binding identity mismatch remains rejected;
- p11: an empty invocation component preserves unrelated callable state; and
- p12: conditional Advance cannot justify unconditional Finish.

Acceptance cases inspect final callable availability and lifecycle witness count,
not only a Boolean result.

The dedicated workflow also replays the existing CALL-019 lifecycle, lifecycle-
aware context, semantic-account, branch-aware context and outcome-continuation
controls under `-Wall -Werror`.

## Boundaries

This repair does not claim:

- complete producer provenance for the separately supplied concrete lifecycle
  bindings;
- new proof of source-path correspondence;
- CLI/native reachability of this API;
- a complete path semantics for every future Surface control construct; or
- any change to may-effect aggregation.

The Rocq proof lane owns the separate source-path correspondence obligation.
Final frozen-snapshot integration/delta validation remains a later audit task.

At authoring, exact-head CI has not yet supplied execution evidence.
