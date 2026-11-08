# FSEM-01 — finite resource-context projection and general frame models

> **Status:** bounded, non-normative implementation and Rocq-model
> correspondence. Tracks [FSEM issue #1613](https://github.com/abiggerhammer/phil/issues/1613).
> General source-to-Core preservation, Haskell Map/Set implementation
> correctness, and universal Haskell-to-Rocq state refinement remain open.

## Why this slice exists

Earlier [two-owner context evidence](formal-semantics-two-owner-context-fsem01-v1.md)
and [single-source two-owner evidence](formal-semantics-two-owner-source-fsem01-v1.md)
established useful one-/two-owner cases. They did not provide a reusable
relation for arbitrarily many unrelated bindings. This slice states that
relation over all **four** Core resource collections:

- Unrestricted map `Map Name Ty` (repeatable read).
- Affine map `Map Name Ty` (optional but non-duplicable consumption).
- Linear map `Map Name Ty` (exactly-once consumption).
- Active shared-loan set `Set Name`.

The proposed finite representation is an ordered list for each map and an
ordered list of loaned owners. **Well-formedness requires** strict ordering
and no duplicate keys within or between structural zones, and that every
loan references a currently held affine or linear owner. Evidence is
rejected if these constraints fail; Haskell `Map.fromList` is not
allowed to normalize an invalid input silently.

## Production executable controls

[Finite Core test](../../test/Phase1FSEM01FiniteContextMain.hs)
builds real `Core.ResourceContext` values through actual production
`Core.insertBinding`, using **3, 7 and 15** distinct names spread
across all three structural modes. It tests exact `Map.toAscList` /
`Set.toAscList` projection, independently implemented finite-list
lookup, reification and full-map/set roundtrips, including absent-name
queries.

Operations are the **real Haskell Core operations**, not implementations
copied from Rocq. The test checks:

- mode-directed insertion and duplicate-name errors across three zones;
- unrestricted read as an exact state identity;
- affine and linear consumption and the complete unrelated-owner frame;
- loan activation/deactivation for both affine and linear owners;
- no consumption of borrowed owners, repeated-loan and missing-loan
  rejection, wrong-mode errors and consumed-linear reuse;
- simultaneous loans on unrelated affine owners while an independent
  linear owner is consumed;
- malformed finite representations: duplicates, cross-zone collisions,
  missing restricted owner for a loan, and noncanonical key order.

Each successful operation compares **every unrelated entry in all four
complete maps/sets**, by removing only the selected owner from the two
states. A matching chosen spectator is not enough to pass.

The source-level accepted and precisely rejected `BorrowEscape` paths
from earlier FSEM-01 remain checked in preflight. Core-supplied affine
modes in this test do **not** claim a new source-level affine type rule.

## Rocq statements and limitations

[SurfaceFiniteContextFrame.v](../../proof/Phil/Surface/SurfaceFiniteContextFrame.v)
introduces `FiniteSnapshot`, ordered-list lookup and loan membership,
`ExactFiniteRelation` over the four extensional Context lookups, and
the explicit `ValidFinite` premises. It proves finite reification has
the four advertised lookup projections, and that the model's
`ForeignFrame` relation is transitive and holds over:

- successful Core-model insertion and linear consumption;
- unrestricted read (identity);
- successful affine consumption in the separately declared model;
- restricted-loan start/end in that model, preserving all unrelated
  bindings and loans;
- borrowed-owner failure in the affine/linear models, and rejection
  of unrestricted-only or already-loaned sources.

The lemmas quantify over **arbitrary finite context sizes** and reuse
the established `Context.v` insertion and linear-consumption theorems.
They do not introduce new admissions or axioms.

The precise trust boundary matters: `Syntax.Ty` is **abstract** in Rocq,
while production Haskell uses concrete `Ty` constructors; Rocq
`Name` is a string, whereas Haskell uses `Text`. `ExactFiniteRelation`
is an explicitly stated *model relation*. The test provides finite,
repeatable checks of the concrete list/Map/Set representation but is
**not a machine-checked proof of Haskell Data.Map/Data.Set or their
universal equivalence to Rocq**. Likewise the affine/loan Rocq models
deliberately use a coarser `option` failure carrier than Haskell's
`CheckError`.

## Early CI gate before full PR CI

The [finite-context early preflight](../../.github/workflows/fsem01-finite-context-preflight.yml)
runs on pushes to **only** `formal-semantics/fsem01-finite-context` before
a pull request is opened. This avoids triggering unrelated PR CI during
initial iteration. Its two jobs:

1. Strictly compile the Haskell library and run the relevant full
   SURF-008 competence regression battery (intrinsic types, callables,
   boundaries, aliases, records, variants, data modes, named types),
   plus prior FSEM-01 two-owner source and flat-product controls and
   the new finite-context test.
2. Compile the Rocq 9.2 finite-context module, checking for new
   admissions/axioms and recording proof hashes.

The Haskell job reuses the merged bounded Hackage update-retry helper
rather than relying on the setup action's unprotected index download.
The PR-triggered copy of this workflow keeps ordinary same-PR
supersession. Full PR CI follows only after preflight acceptance.

## Open FSEM-01 obligations

General source-level affine typing, nested ownership and products,
real source join/capture/loop transitions, exact failure-state
simulation, and universal finite Haskell-to-Rocq refinement remain
unproved. `satisfies C`, effects and assurance authority have their
own explicit FSEM-04/06/07 scope; this slice does not discharge them.
