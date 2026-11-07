# FSEM-01 — source, production loan-state, and Rocq correspondence (proposed v0)

> **Status: proposed correspondence relation and open proof obligations.** This is
> a review artifact for [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613),
> **not** an adopted source typing judgment, a verified source-to-Core translation,
> or a general soundness theorem. It follows the executable
> [FSEM-01 production bridge](formal-semantics-borrow-resource-bridge-fsem01-v1.md)
> merged in [#1622](https://github.com/abiggerhammer/phil/pull/1622).
> Exact tested PR head: `1a9f4c64863201553fc7c87c755710fdfb21588b`
> (80 successful PR workflow runs); merged squash:
> `5283d65545de79ee975ad38b5af4ddd0c056cb48`.
> These are **test results**, not a source/model correspondence certificate.

## Claim boundary

The admitted bridge is deliberately smaller than Phase 1 source semantics.
It handles one parsed Grammar-v1 function with exactly one parameter and an
exactly matching result type, both independently resolved as **intrinsically
linear** `Bytes[N]`, followed by one lexical borrow-expression statement and
an exact return of the same owner. Its borrow body consists only of supported
local view occurrences and the `unit` expression; unsupported forms return
`Nothing` (non-competence). Generic parameters, requirements, arbitrary
global references, captures, effects, aliasing, nested borrows, branches, and
loops are **not** admitted. The `satisfies C` clause is parsed but its
obligations are **not** discharged by this adapter.

These accepted/rejected *bounded checker* witnesses have the same parameter
and result type and the same outer `return owner;`:

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { view; unit; };
  return owner;
}
~~~

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { view; };
  return owner;
}
~~~

The first reaches terminal `Return (TyBytes (RefNat 8))`. The second must
report the production `BorrowEscape` class with detail
`shared view escapes its lexical scope`: its **borrow body result** contains
the borrowed view. Neither outcome certifies the complete source declaration.

## Three identity and state domains (do not conflate them)

| Domain | Actual representation | Role and boundary |
| --- | --- | --- |
| Parsed source/local resolution | `GrammarV1BinderKey (DeclarationKey, Int)` in [BinderScope.hs](../../src/Phil/Surface/GrammarV1/BinderScope.hs) | A declaration-rooted, monotonically allocated binder ordinal; spelling/span and binder kind are metadata, not identity. The owner is resolved in the parent frame, then the fresh view in a child frame. |
| Production surface/resource checker | `Name` keys in `SurfaceState.stateBindings` and `Phil.Core.Context.ResourceContext`, whose `linearBindings` and `sharedLoans` track owners | `grammarV1ResolvedBinderCoreName` injectively encodes the source key as a generated name; the adapter installs a single `InitialBinding Linear (TyBytes ...)` under the owner name and projects the view occurrence to its **own** generated name. A loan is keyed by **owner Name**, not by view Name. |
| Normalized Rocq proof models | `ResourceOwner := nat`, `LoanSet := ResourceOwner -> bool` in [ResourceJoin.v](../../proof/Phil/Core/ResourceJoin.v) / [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v) | Abstract owner/slot/loan projections. The repository has **not** supplied a certified encoding of these `nat` owners from the source binder keys or production `Name`s, nor a proof of transition preservation. |

`TyBytes(8)` equality is **type** evidence. It does not establish owner
identity, lexical scope, value non-escape, or the model's subject/slot
succession relation. Similarly, the view binder has its own key/name but the
shared-loan set records the **owner** it borrows.

### Concrete projection currently implemented

For a fixed declaration lineage `D`, let `k_o` be its one source owner
parameter key, `k_v` its fresh view key, and `N(k)` its generated
`Core.Name`. For this admitted function shape the implementation:

1. Checks `Bytes[N]` on parameter and result independently through
   [CheckedType.hs](../../src/Phil/Surface/GrammarV1/CheckedType.hs);
   requires `Linear` and exact type equality.
2. Allocates `k_o` in [BinderScope.hs](../../src/Phil/Surface/GrammarV1/BinderScope.hs);
   resolves the borrow owner **before** allocating `k_v` in
   [BorrowViewScope.hs](../../src/Phil/Surface/GrammarV1/BorrowViewScope.hs).
   It checks the owner and outer return against the same `k_o`, and only
   accepts body occurrences resolved to `k_v`. The child lexical frame
   disappears after the borrow; its ordinal is not reused.
3. Builds a synthetic [surface component](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs)
   with initial binding `N(k_o)`, borrow owner `N(k_o)`, view binder
   `N(k_v)`, and final return `N(k_o)`; no source spelling is installed as
   a semantic resource key. This is a bounded adapter into an **existing**
   checker, not general Grammar-v1 elaboration.
4. Invokes [checkSurfaceComponent](../../src/Phil/Surface/Check/Engine.hs).
   It may return a production check failure or succeed with exact terminal
   `Return (TyBytes ...)`; it does **not** expose a verified transition trace.

The generated name construction is length-prefixed by declaration-root text
and appends the local ordinal. Any future correspondence proof must
distinguish this Haskell-level construction from a proved cross-language
encoding of Rocq `ResourceOwner`s.

## Observable production checkpoints: one admitted path

Use `o = N(k_o)`, `v = N(k_v)`, `T = TyBytes(RefNat 8)`, and
`C = resourceContext (stateCore state)`. The following describes the
**implementation's control flow** in
[Engine.evalBorrow](../../src/Phil/Surface/Check/Engine.hs) and
[Core.Context](../../src/Phil/Core/Context.hs); it is **not** a separately
proved small-step semantics. The current public result records only terminal
controls, not snapshots of `C`.

| Cut | Production state/action | Scope/value obligation |
| --- | --- | --- |
| B0 — entry | `linearBindings C[o] = Just T`; `o` is not in `sharedLoans C` | Only `k_o` is in the enclosing source frame. `v` is not yet available. |
| B1 — start | `startSharedLoan o` inserts `o` into `sharedLoans C` without consuming the linear owner. An unrestricted view binding `v` has `BorrowedViewShape o ...`. | The view is visible only within the child scope. Owner and view are **distinct** binders. |
| B2 — body result | `checkScopedValueBlock` checks/prunes child locals, retaining the resulting runtime value. `view; unit;` ends with `RuntimeUnit`; `view;` ends with a `BorrowedViewShape o ...` result. | The view's *result identity/shape*, not just name spelling, must be tested for escape. |
| B3 — close (positive) | `containsBorrowedView o` is false; `endSharedLoan o` removes the loan membership. The owner is still present in `linearBindings C`. | The child view has left scope and does not escape as a result. The **borrow closure** is a continuing point before the outer return. |
| B3' — reject (negative) | `containsBorrowedView o` is true; `evalBorrow` returns `BorrowEscape` before `endSharedLoan` and before the outer return. | No accepted post-borrow state or successful terminal control exists for this path. |
| B4 — outer return (positive only) | `return owner;` consumes the linear `o` via `useBinding` / `consumeLinear`; terminal completion checks its resource residue; reported control is `Return T`. | A terminal return is **not** a continuing join/backedge predecessor. |

This account is intentionally sequential. The production checker also rejects
an attempted linear owner consumption while the loan remains active
(`OwnerBorrowed` in `Core.Context`), and recognizes borrowed views inside
runtime tuples, but neither general source shape is admitted/tested through
this particular FSEM-01 adapter.

## Candidate source-to-model relation — **not discharged**

To connect B0–B3 to a model theorem, an eventual relation must define (at
least) all the following. They are **proposed proof inputs**, not implemented
runtime functions or established equalities:

- An exact source-binder map `N : BinderKey -> Core.Name` with proven
  distinctness and occurrence preservation for the admitted elaboration.
- An explicitly chosen **injective-on-live-owners** representation
  `I : Core.Name -> ResourceOwner` into Rocq's `nat` carrier. It must
  distinguish separate owners with equal `Ty` and must not map the view's
  separate binder to an additional owning loan.
- At each cut at which the relation is claimed, a loan-membership condition:
  `L_model (I o) = true` iff `o` belongs to `sharedLoans C`.
  For non-owner identifiers, `L_model` must not invent loans.
- A corresponding **live linear owner** and mode/type relation between
  `linearBindings C`, `surfaceInitialBindings`, and the model's
  `projectionIncomingLinear` where a continuing projection is applicable.
  `projectionBindings`, `projectionSubjectOf`, fixed-slot requirements,
  and `SuccessionEvidence` need *separate* witnesses; type agreement alone
  supplies none of them.
- A step relation or simulation showing that lexical scope introduction,
  `startSharedLoan`, value-result inspection, `endSharedLoan`, and
  `consumeLinear` preserve the appropriate relation, with the negative
  `BorrowEscape` path mapped to **rejection**, not to an accepted state.

The relation must be indexed by an **admitted source fragment**, an exact
declaration lineage, and a precise production state/step. `Nothing`
(non-competence), `Left` (lexical/focusing/production error), successful
continuation, and terminal return are distinct outcomes. In particular, an
absent local cannot be silently replaced with a global or a guessed owner.

### Why the current Rocq theorem is not yet this result

[ResourceScope.v](../../proof/Phil/Core/ResourceScope.v) defines
`LexicalLoansClosedAtBoundary` and
`ScopedBoundaryProjectionSuccess`, combining a successful normalized
`ResourceProjection` with a loan-free **ordinary join or loop backedge**.
It proves `scoped_loan_cannot_cross_continuing_boundary` and its join/
backedge corollaries. [ResourceJoin.v](../../proof/Phil/Core/ResourceJoin.v)
separately constrains live linear owner projection and subject/slot
continuity. Neither theorem quantifies over a Grammar-v1 AST, `BinderKey`,
`Core.Name`, or Haskell's `startSharedLoan`/`endSharedLoan` transitions.

**B3 is a borrow-expression exit**, not automatically
`OrdinaryJoinBoundary` or `LoopBackedgeBoundary`; B4 is a **terminal
return**. Therefore the existing theorem must not be instantiated at B3 or
B4 merely by calling them boundaries. A future proof may define the
appropriate borrowed-region closure relation and separately connect it to
continuing projections where the source control flow genuinely has a join
or backedge. Terminal arms have their own
`terminal_arm_contributes_no_continuing_projection` theorem.

## Evidence classification and review gates

| Claim | Current evidence | Status |
| --- | --- | --- |
| Exact owner/view lexical keys, parent/child visibility, no active shadow | [SURF-009 tests](../../test/Phase1GrammarV1BorrowViewScopeMain.hs), [BinderScope.hs](../../src/Phil/Surface/GrammarV1/BinderScope.hs) | Executable bounded lexical evidence, **not** the full resource semantics |
| Intrinsic linear mode and exact owner-return type in admitted bridge | [BorrowResourceSurface.hs](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs), [FSEM-01 tests](../../test/Phase1FSEM01BorrowResourceMain.hs) | Implementation + exact-head CI |
| Positive loan closure; negative escaped body result classified by production `BorrowEscape` | [Engine.hs](../../src/Phil/Surface/Check/Engine.hs), [FSEM-01 tests](../../test/Phase1FSEM01BorrowResourceMain.hs) | Executable checker tests; no exported transition certificate |
| Closed lexical loans on normalized continuing joins/backedges | [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v), [ResourceJoin.v](../../proof/Phil/Core/ResourceJoin.v) | **Existing Rocq theorems in abstract models**, not source-to-model preservation |
| The proposed identity, state, step and error correspondence above | No implementation of `I`, no source/production-to-Rocq simulation proof | **OPEN — not proved or certified** |
| Full source declaration, `satisfies C`, arbitrary branches/captures/aliases, complete Phase 1 progress/preservation | Not covered by the FSEM-01 bridge or this document | **OUT OF SCOPE** |

For a future implementation/proof PR, acceptance requires:

1. A machine-checkable extraction/simulation boundary, naming all
   assumptions and its TCB, not a comparison of pretty-printed owner names.
2. A testable transition/trace witness (or equivalent checker certificate)
   for B0–B4 and B3', with **exact source provenance**, stable owner identity,
   and matched legal/illegal result types; reject failures for the stated
   `BorrowEscape` cause rather than accepting any error.
3. An actual model extension or theorem connecting source borrow exit to
   loan closure **before** attempting any ordinary-join/loop lemma; terminal
   returns must not be reclassified as continuing predecessors.
4. Separate coverage for owner-move-while-loaned, aggregate/captured view
   escape, nested scopes, affine disposal, joins/backedges and effectful paths
   before expanding the claim. No blanket compiler correctness is implied.
5. Exact-head CI/theorem evidence and an accepted corresponding Logic Ledger
   / Conformance Matrix entry **only when** an obligation is really
   discharged. This proposed relation alone changes neither authority.

**Bottom line:** #1622 ties a small parsed-source loan to the actual
production checker and isolates a real `BorrowEscape` negative. The missing
work is a precise, proved mapping of that implementation's identities,
states, transitions and rejection outcomes to the normalized Rocq model.

## Subsequent executable production checkpoints

The [FSEM-01 production loan-state trace](formal-semantics-loan-transition-trace-fsem01-v1.md)
makes the bounded B0–B4 and B3' production states observable by the **same**
borrow evaluator as the ordinary checker. Its concrete `Core.Name`,
`linearBindings` and `sharedLoans` checkpoints and negative error prefix
are runnable evidence for constructing an eventual model correspondence.
The source-to-Rocq owner encoding and simulation theorem remain **open**.

## Subsequent first proof slice

[The exact linear loan transition model](formal-semantics-exact-loan-transition-model-fsem01-v1.md) adds Rocq theorems about owner-name loan membership, preserving unrelated bindings, blocked linear consumption, and a **conditional** relation to abstract ResourceOwner loan sets. Its name/owner encoders are injective *hypotheses*, not verified Haskell source-to-model functions; it does not prove escaping-value rejection or a source-to-Rocq simulation. Review the exact-head CI evidence separately.
