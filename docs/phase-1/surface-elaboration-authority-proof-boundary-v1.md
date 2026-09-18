# PHIL-SURFACE-ELAB-001 proof boundary

This slice certifies the Phase-1 Grammar-v1 semantic elaboration authority boundary.

It starts after a Grammar-v1 construct exists. It does not prove parser soundness/completeness. The certified invariant is that elaboration either:

- preserves the exact intended semantic category and routes to the exact competent semantic checker/handoff; or
- rejects at that exact competent handoff rather than succeeding through a category collapse or unsupported implementation path.

For lineage-bearing constructs, the stable DeclarationKey/InstanceKey/ProcessKey input is consumed exactly and is not recomputed from source position.

Elaboration may insert deterministic plumbing, but it may not synthesize evidence, authority, qualification, assumptions, or realization choices. The Phase-1 semantic attribute namespace is closed: unknown/conflicting attributes reject rather than becoming implementation-defined semantic hooks.

The dedicated correspondence workflow replays the established SURF-008 Grammar-v1 elaboration regressions across types/propositions/references, generic requirements, callables, providers, functions/components, protocols/boundaries, architecture/program/process surfaces, plus the portable lineage/semantic-attribute regression.

Explicit boundaries remain:

- parser/Grammar-v1 language correspondence (PHIL-SURFACE-GRAMMAR-CORR-001);
- binder-dependent name/scope resolution (SURF-009 / PHIL-SURFACE-BINDER-SCOPE-001);
- category-specific semantic checker truth;
- verification/assurance authority;
- provider/runtime qualification and evidence;
- target/Systems realization; and
- concrete Haskell Text/Map/AST representation and GHC/runtime correctness.
