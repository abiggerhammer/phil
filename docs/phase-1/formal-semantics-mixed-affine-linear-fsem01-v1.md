# FSEM-01 — one parsed source function with affine and linear ownership

> **Status:** bounded, non-normative source-to-production-checker witness plus
> separately checked Rocq extensional model lemmas. Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613).
> This does **not** claim full Haskell-to-Rocq implementation refinement,
> source type preservation, or discharge of the declared satisfies-C obligation.

## Why this successor is different

[#1666](https://github.com/abiggerhammer/phil/pull/1666) admitted an exact
nominal affine Permit into a real single-parameter production Surface checker
path. [#1655](https://github.com/abiggerhammer/phil/pull/1655) checked two
linear Bytes owners in a single parsed function. Neither placed **both
structural modes in the same source-derived run**. The present slice does.

A source witness:

~~~phil
data Permit mode affine = Permit(U64);
fn use(permit : Permit, payload : Bytes[8]) -> Bytes[8] satisfies C {
  borrow permit as view { view; unit; };
  return payload;
}
~~~

The source-level Permit mode is **not an authority by spelling**. The existing
grammar-v1 nominal checker must first receive an independently admitted
external lifecycle/resource justification. Absence or unadmitted evidence
rejects the declaration; an Unrestricted nominal mode cannot weaken a Linear
Bytes[8] payload. The nominal mode and type used for the first parameter are
resolved using its exact GenericTypeKind, DeclarationKey and
InterfaceRevision. The second parameter is **independently source-checked**
as intrinsic Linear Bytes[N]. Both binders are allocated through a single
function's source-rooted lexical scope. Only then are the two checked modes
installed in **one actual production** SurfaceEnvironment and checked.

[The bounded mixed adapter](../../src/Phil/Surface/GrammarV1/SourceAffineResource.hs)
explicitly recognizes a nonrecursive function with exactly two term parameters,
one lexical borrow of the affine parameter, and a return of its exact linear
parameter, the affine parameter, or Unit. It rejects unrelated expression
shapes, other borrows, wrong result types, recursive functions, generic
requirements and unsupported control flow as **non-competence**, not as an
implicit generic acceptance. The same production component is checked both
with and without trace recording; the results must agree.

## Executable source acceptance and precise rejection

[The native regression driver](../../test/Phase1FSEM01MixedAffineLinearMain.hs)
parses the eight source fixtures in
[the mixed ownership corpus](../../test/fixtures/fsem01-mixed-affine-linear-v1/):

- *accepted.phil*: borrow/close the affine Permit, return and consume Linear
  Bytes exactly once. The Permit remains live in the affine zone, and native
  Core.ensureComplete accepts function exit because there is **no linear
  debt**. This proves permission to *leave affine unused*, not that a separate
  concrete destructor executes.
- *escape.phil*: remove the borrow body's final unit statement, producing
  precisely BorrowEscape and no invented after-rejection successor; both
  owners remain in their original structural zones and the Permit loan
  remains active.
- *leak-linear.phil*: return Unit instead of the linear payload. The production
  checker rejects LinearCompletion with the exact
  UnconsumedLinearResources payload; the trace ends at loan-close.
- *return-affine.phil*: consume/return the affine Permit instead; the same
  undischarged Linear Bytes obligation rejects return.
- *unjustified.phil*: source mode affine without independent admitted
  attestation rejects as StrongerModeMissingJustification; an explicitly
  unadmitted attestation also rejects.
- *weakened.phil*: mode unrestricted attempting to weaken a linear payload
  rejects as DeclaredModeWeakensDerived.
- *wrong-return.phil* and *wrong-borrow.phil*: an incompatible declared
  return width and a borrow of the linear rather than affine source parameter
  are outside this deliberately narrow adapter's competence.

The driver independently builds **actual** Core.ResourceContext states from
each real production checkpoint and compares all unrestricted, affine, linear
and active-loan collections. It tests that consuming the linear spectator
while the Permit is loaned leaves the affine map and loan bit intact; consuming
the borrowed Permit is OwnerBorrowed, and reusing already-consumed Bytes
is UnknownBinding. The accepted return has an empty linear zone and the
still-live affine binding. The negative return paths test Core.ensureComplete
against the exact still-live linear binding.

## Conditional Rocq frame/debt theorems

[SurfaceMixedAffineLinearBridge.v](../../proof/Phil/Surface/SurfaceMixedAffineLinearBridge.v)
composes the earlier finite-context frame lemmas with the admitted affine
mode gate. It proves:

1. Source affine admission has an explicit external admission premise.
2. Borrowing an affine owner frames any distinct live linear spectator and
   its independent loan state.
3. The borrowed affine owner cannot be consumed, while the linear spectator
   remains live.
4. Independently consuming a linear owner preserves a distinct affine
   owner and any active loan on it.
5. Closing a loan to the affine owner leaves an outstanding linear binding.
6. Even modeled disposal of the unloaned affine owner leaves linear debt
   untouched.

These are **extensional Rocq Context model** statements, not a universal
simulation theorem for native Data.Map, Data.Set, Text, actual checker
failures, or concrete source AST. Rocq's abstract Syntax.Ty and String-based
names remain distinct from native Haskell representation. The external
lifecycle attestation's soundness is explicitly not proved.

## Verification and the next gap

A narrowly branch-scoped [early preflight](../../.github/workflows/fsem01-mixed-affine-linear-preflight.yml)
runs before opening a PR: strict warning-free production Haskell library,
existing SURF-008 and relevant FSEM-01 regressions, new executable witnesses,
and Rocq 9.2 compilation with a no-new-admissions check and printed
assumptions. The usual exact PR-head suite and FSEM claim guard follow.

**Still open:** actual source-level nested/nominal products and elimination,
mixed multi-owner joins/loops/captures, general affine constructor semantics,
universal native-to-Rocq state and error-path simulation, full
satisfies C assurance authority, and FSEM-05's independently executable
Rocq reference interpreter with complete admitted-construct coverage.
