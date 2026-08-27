# Phase 1 surface parser production corpus v1

## Purpose

This corpus fixes concrete parser expectations for Grammar-v1 forms introduced or repaired by the Phase 1 surface reconciliations. It is a specification target for SURF-002, not evidence that the current Haskell parser already implements Grammar v1.

## Authority and competence

`grammar/phase1-surface.ebnf` remains the sole concrete-syntax authority. The fixtures under `test/fixtures/phase1-surface/` are examples classified against that grammar.

An `accepted` fixture asserts only that a conforming parser consumes the whole file and produces a surface structure. It does **not** assert that name resolution, elaboration, typing, resource checking, assurance, or lowering succeeds.

A `rejected` fixture is deliberately malformed so rejection belongs at the syntax layer. A parser must not accept it and rely on a later semantic checker to notice the problem.

## Coverage

The original grammar/type-system reconciliation cases cover refinement types, explicit transport, native finite membership/disjointness, term-level `offer`, branch-sensitive callable residues, exact replacement callees, and composition among those forms.

The structural-mode reconciliation covers declaration-level mode spelling for records/sums, all three explicit capability possession modes, ordinary type-derived binding mode, and syntax-negative attempts to put mode in the wrong place.

The broader syntax/semantics completeness pass adds parser pressure for:

- `Type` static actuals;
- static `Session` parameters/actuals and named session references;
- the full admitted generic requirement categories for authority, boundary representation, representation, placement, cost, and environment;
- specialized static contract references in contract-bearing positions;
- product/tuple types and tuple values, distinct from grouping;
- explicit callable outcome classification (`success`, `negative`, `terminal`, `fatal`);
- callable-wide and per-outcome residual `obligation` clauses;
- explicit stricter closure mode;
- join invariants;
- typed loop-state initializers;
- standalone typed-negative `reject`.

Each repaired boundary has at least one positive parser fixture and a nearby syntax-negative case where a useful malformed form exists. Semantic no-weakening, kind/sort correctness, outcome compatibility, obligation disposition, resource projection, session duality, authority possession, and assurance validity remain checker obligations.

## Manifest

`manifest.json` is the machine-readable integration point for the future canonical Haskell parser harness. Each row has a stable corpus ID, relative path, parse expectation, grammar productions exercised, and whether semantic checking is deferred.

SURF-002 implementation should consume this manifest rather than duplicating the fixture list in Haskell. Whole-file consumption is mandatory. The harness should report the fixture ID and path on disagreement.

The integrity checker requires every `.phil` fixture on disk to appear exactly once in the manifest, so adding an untracked example or leaving a stale manifest row fails CI.

## Deliberate non-goals

This corpus does not:

- define semantic acceptance;
- prescribe the future surface AST shape;
- require a particular parser library or backtracking strategy;
- duplicate Grammar v1 as another grammar;
- add parser recovery behavior; or
- claim parser/grammar soundness or completeness by testing alone.

The semantic-to-surface classification is recorded in `syntax-semantics-completeness-v1.md`. The later parser-correspondence proof/certificate remains responsible for the stronger SURF obligation. The corpus is executable pressure and regression evidence for that work.
