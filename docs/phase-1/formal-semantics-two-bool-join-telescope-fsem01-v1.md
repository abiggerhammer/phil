# FSEM-01 — source-checked two-slot Bool join telescope

> **Status: bounded, non-normative implementation slice under review.**
> Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613), matrix
> R10/R11/R15, and follows the merged
> [one-slot Bool join](formal-semantics-bool-join-telescope-fsem01-v1.md).
> Do not infer FSEM-01 exit, FSEM-05 execution, FSEM-06 implementation
> refinement, or normative Phase 1 graduation from this checked fragment.

## Exact admitted source witness

The new bounded adapter accepts a non-generic, nonrecursive source function
with two Unrestricted Bool parameters, one Linear Bytes[N] spectator,
two continuing predecessor blocks each ending in an **actual two-element
tuple of source-local variables**, two Unrestricted Bool post-join slots,
two checked uses of those slots, and a single terminal return of the original
Linear Bytes[N] owner:

~~~phil
fn choose(flag : Bool, alternative : Bool, payload : Bytes[8]) -> Bytes[8] satisfies C {
  if flag join state (selected : Bool, companion : Bool) invariant selected == selected {
    (flag, alternative);
  } else {
    (alternative, flag);
  };
  selected;
  companion;
  return payload;
}
~~~

The two branches deliberately provide **different positional values**. A typed
join-state slot does not mean the predecessor values are equal. The checked
lexical authority [LetPatternScope](../../src/Phil/Surface/GrammarV1/LetPatternScope.hs)
resolves both flat tuple occurrences to exact predecessor binders in the
pre-join scope. The unchanged [JoinStateScope](../../src/Phil/Surface/GrammarV1/JoinStateScope.hs)
allocates both state binders in declared order after both predecessor scopes
close, checks slot type-reference availability before each binding, and
checks invariant references after the complete telescope.

## Native production resource sequence

The new [source bridge](../../src/Phil/Surface/GrammarV1/SourceTwoBoolJoinTelescope.hs)
independently checks both declared slot types with
[CheckedType](../../src/Phil/Surface/GrammarV1/CheckedType.hs) as
Unrestricted Bool. The opt-in [production Engine entrypoint](../../src/Phil/Surface/Check/Engine.hs)
then runs:

1. Both branch tuple expressions through real production
   \`checkValueBlock\`/\`pruneScopedPath\`, independently requiring an actual
   two-element \`RuntimeTuple\` of Unrestricted Bool scalar values.
2. The validated predecessor contexts through \`joinExclusive\` and native
   \`Core.Context.joinContinuing\`, preserving the exact four resource
   collections (Gamma/Affine/Linear/loans).
3. Two **separate** production \`insertBindingMeta\` /
   \`Core.Context.insertBinding\` operations, in source declaration order,
   with a real first-bound and both-bound checkpoint. Neither is installed
   before the resource join succeeds.
4. Explicitly justified \`true\` or an exact source-reflexive slot equality,
   rejecting \`false\` or unproved cross-slot equality as
   production \`MissingEvidence\` **after** both inserts and before successor
   statements.
5. Both original checked post-join slot reads, then one return of the Linear
   Bytes spectator.

The ordinary and independently tracing production runs must have identical
outcomes. No joined or bound successor may be invented after a bad predecessor
tuple, failed Core resource join, or failed insertion.

## Source tests and model proof

[The strict test driver](../../test/Phase1FSEM01TwoBoolJoinTelescopeMain.hs)
loads [23 parsed-source fixtures](../../test/fixtures/fsem01-two-bool-join-telescope-v1/accepted-reflexive.phil).
Accepted examples exercise different, same and repeated unrestricted source
operands, literal-true and reflexive first/second slot proofs. Negative source
controls separately replace the first/second operand of each predecessor with
Linear Bytes and require exact \`TypeMismatch\` before any Core join or
post-join binder. Other controls test false/cross-slot \`MissingEvidence\`,
source binder collisions, pre-join slot access, unsupported slot modes or
arity, missing invariant/else, and incorrect successor use. Adapter refusal
(\`Nothing\`) means **noncompetence**, not normative invalidity.

The conditional Rocq file
[SurfaceSourceTwoBoolJoinTelescope.v](../../proof/Phil/Surface/SurfaceSourceTwoBoolJoinTelescope.v)
composes prior [one-slot lemmas](../../proof/Phil/Surface/SurfaceSourceBoolJoinTelescope.v):
tuple order follows the same selected branch; two successful source-supplied
insertions require distinct names and preserve the first exact checked slot;
every linear spectator lookup is unchanged by either insertion, and closed
loans remain closed. The source Haskell test exercises actual production
Map/Set behavior; the Rocq proof is a conditional normalized model of those
operations, not an extracted checker implementation refinement.

## Unproved by this slice

Dependent and greater-than-two-slot telescopes; affine/linear phi values,
mixed-mode tuples, general invariant search, actual runtime phi evaluation,
nested/match/capture/loop source behavior, arbitrary nonlocal source
expressions, full Text/Map/Set-to-Rocq representation, error class preservation
for every program, and \`satisfies C\` assurance discharge remain open.
FSEM-02 owns session progression; FSEM-05/06/07 are separate obligations.
