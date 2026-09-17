# PHIL-EXEC-BIND-001 proof boundary

This slice certifies the bounded Phase 1 semantics already implemented by SURF-009, EXEC-005, EXEC-006, EXEC-010, and EXEC-014. It does **not** introduce mutable locals, implicit destructors, or a general-purpose `free` operation.

## Certified semantic boundary

`proof/Phil/Core/BindingSemantics.v` establishes:

- local semantic binder identity is declaration-root plus monotonic lexical ordinal; display spelling and source position are diagnostic only;
- duplicate binders and active lexical shadowing reject; closed sibling scopes may reuse spelling only with a fresh semantic ordinal;
- a semantic value must be initialized before source-significant observation;
- reserving target storage does not initialize a Phil value;
- a semantic value identity cannot be initialized twice in place, so ordinary source bindings are immutable and semantic updates use successor identities;
- initialization into realization storage requires that exact storage to have been reserved;
- affine/unrestricted structural discard is semantically empty, while linear discard rejects;
- structural discard may not hide source-visible effects, failures, or resource transitions; physical reclamation stays a realization fact;
- structural restrictedness alone does not create release competence;
- `release` requires a unique applicable declared transition, satisfied prerequisites, owner consumption, a non-branch-sensitive deterministic outcome, and preservation of the exact semantic account.

`proof/Phil/Core/BindingSemanticsImplementation.v` certifies the finite conjunction/fail-closed decision surface corresponding to those independently checked production facts.

## Production correspondence

The unchanged production authorities remain:

- `Phil.Surface.GrammarV1.BinderScope` for declaration-rooted binder keys, no-active-shadowing, sibling-scope freshness, and exact local resolution;
- Grammar-v1 parser/checker rejection of source reassignment;
- `Phil.Systems.SemanticInitialization` for exact StageContract-bound initialization/observation order;
- `Phil.Systems.StructuralDiscard` for no-hidden-finalizer StageContract correspondence;
- `Phil.Surface.Check.Types.selectReleaseTransition` plus the Surface engine for exact resource-specific release competence and owner consumption.

The dedicated CI gate rebuilds the complete Haskell substrate and replays the existing SURF-009 / EXEC-005 / EXEC-006 / EXEC-010 / EXEC-014 regression corpora unchanged.

## Explicit retained boundaries

The proof does not claim correctness of concrete `Text`, `Map`, or `Set` representations, parser source-span construction, `DeclarationKey` persistence, StageContract serialization/digests, release-transition registry construction, authority/evidence/assumption truth, target physical reclamation, GHC/runtime behavior, Rocq/toolchain behavior, or backend execution. Those remain named representation, evidence, or TCB boundaries.

General shadowing ergonomics, source mutable locals, and a general unsafe escape hatch remain deferred. Implicit finalization is not deferred semantics: it is rejected unless expressed as an explicit competent resource transition.
