# FSEM-01 — exact owner/loan transition model (first proved slice)

> **Scope:** a *conditional*, machine-checked Rocq correspondence between
> the existing exact `BinderKey` model, the Name-keyed
> `Phil.Core.Context` resource-state model, and the normalized loan-owner
> carrier from `ResourceScope.v`. This is **not** a proof about the compiled
> Haskell checker, the complete Grammar-v1 elaborator, or an adopted Phase 1
> typing rule. Track the remaining obligations in [#1613](https://github.com/abiggerhammer/phil/issues/1613)
> and the [FSEM-01 state correspondence inventory](formal-semantics-loan-state-correspondence-fsem01-v0.md).

## Model and mechanized claims

The new [SurfaceBorrowLoanStateCorrespondence.v](../../proof/Phil/Surface/SurfaceBorrowLoanStateCorrespondence.v)
uses the **existing** `Phil.Core.Context.ResourceContext` record (functional
lookups for linear bindings and shared loans), not a second ownership type.
It introduces `startLinearSharedLoan` and `endLinearSharedLoan` as
functional models of the **linear-owner branch** of the Haskell
[Core.Context.startSharedLoan/endSharedLoan](../../src/Phil/Core/Context.hs)
operations.

The functions only change the loan bit for an exact `Syntax.Name` and do
**not** mutate the unrestricted, affine, or linear binding maps. Starting
a loan requires the owner's linear binding to exist and the loan not to be
active. Ending a loan requires an active loan. Mode/type derivation remains
a separate check in the
[production FSEM-01 adapter](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs).

The proved properties (subject to successful exact-head CI compilation) are:

| Proof/theorem | Precisely what it establishes |
| --- | --- |
| `start_linear_loan_requires_present_unloaned_owner` / `end_linear_loan_requires_active_owner` | Successful model transitions require an existing linear owner/not-active loan or an active loan, respectively; they have exact owner loan-bit effects and preserve linear bindings. |
| `set_core_loan_preserves_other_names` / `set_core_loan_preserves_all_binding_maps` | No unrelated loan or resource-map mutation is introduced by the model transition. |
| `started_linear_loan_blocks_owner_consumption` | The existing `Context.consumeLinear` Rocq model produces `OwnerBorrowed` while the newly started loan is active. |
| `end_after_start_restores_loan_membership` | Starting and closing an initially inactive owner's loan restores *all* extensional loan membership and preserves its linear binding map. |
| `exact_loan_relation_preserved_by_one_name_update` | Updating a Name-keyed loan set and the normalized natural-number owner loan set agrees for **all represented binder keys**, provided both encodings are injective and initially related. |
| `start_linear_loan_preserves_exact_owner_relation` / `end_linear_loan_preserves_exact_owner_relation` | Under the same explicit injection/relation hypotheses and the step's concrete success preconditions, the two carriers remain related after start/end. |
| `admitted_view_name_differs_from_exact_owner` / `admitted_borrow_resolves_the_same_exact_owner_key` | Given the modeled earlier owner ordinal and later view ordinal, the borrowed view gets a distinct generated identity; the checked borrow still resolves the original owner key. |

## Exact conditional relation

Given two supplied functions and explicit injectivity hypotheses,

- `nameOf : BinderKey -> Syntax.Name`
- `abstractOwnerOf : BinderKey -> ResourceOwner`,

the relation is, for **every represented binder key** `k`:

~~~text
sharedLoans(context, nameOf(k)) = modelLoans(abstractOwnerOf(k))
~~~

A loan update at `nameOf(ownerKey)` corresponds to an update at
`abstractOwnerOf(ownerKey)`. Separate name/owner injectivity is necessary:
type equality alone cannot distinguish two owners, and a view binder is
**not** a second owner/loan. The proof models all represented keys, not
just the chosen target, but does **not** establish surjectivity or absence
of loans for names outside the represented domain.

The source binder semantics used here come from
[BindingSemantics.v](../../proof/Phil/Core/BindingSemantics.v) and
[SurfaceBorrowViewScope.v](../../proof/Phil/Surface/SurfaceBorrowViewScope.v).
The normalized abstract loan carrier is
[ResourceScope.LoanSet](../../proof/Phil/Core/ResourceScope.v), **not**
an instantiation of the continuing-boundary `ScopedBoundaryProjectionSuccess`
relation.

## Explicit unproved boundaries

1. The **actual Haskell** `$phil.local` Name encoder and the translation
   of persisted `DeclarationKey` + ordinal into Rocq `BinderKey` remain
   outside the proof. `nameOf` and `abstractOwnerOf` are universally
   quantified *with hypotheses*, not constructed adapters.
2. The extensional Rocq `Context` models Haskell's finite maps and sets,
   but no extraction or implementation refinement theorem is established
   for `startLinearSharedLoan`/`endLinearSharedLoan`. In particular,
   the Haskell checker has broader affine and pending-receive cases.
3. The model covers loan **membership**, linear owner presence, and the
   owned/view *identifier distinction*. It does not model the runtime value
   tree, `containsBorrowedView`, `BorrowEscape` diagnostic, scoped
   pruning, source result checking, capture, nested loans, or effectful
   execution paths. #1622 supplies a **bounded executable** negative test,
   not the missing proof.
4. `ResourceScope.v` proves closure at normalized continuing joins and loop
   backedges; a borrow-expression exit and a terminal return are different
   control boundaries. These theorems do not conflate them.
5. `satisfies C` and source-level certification remain undisputed open work;
   the current proof does not silently discharge a contract.

## Exact-head proof control

[.github/workflows/fsem01-exact-borrow-loan-state.yml](../../.github/workflows/fsem01-exact-borrow-loan-state.yml)
compiles dependencies and the new theorem file with **Rocq 9.2.0**, rejects
`Admitted`/`Axiom`/`Parameter` declarations in the new proof file, and
records source, compiled `.vo`, and document SHA-256 digests.

Only a **green check on the final PR head** establishes that the proposed
statements compiled. The remaining source/Haskell-to-model implementation
correspondence must be checked separately before strengthening the claim.

## Later exact binder-name representation slice

[The FSEM-01 binder-name encoding proof and production Text conformance](formal-semantics-binder-name-encoding-fsem01-v1.md) adds a Rocq roundtrip/injectivity theorem for the exact ASCII length-prefix serialization shape and executable Haskell checks of the actual `GrammarV1BinderKey` → `Core.Name` producer, including Unicode roots. The `Data.Text`/Rocq `String` and persisted declaration-root representation bridges remain open; the name injection premise is not claimed globally for the concrete Haskell implementation.
