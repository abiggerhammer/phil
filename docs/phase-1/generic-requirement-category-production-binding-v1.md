# Generic Requirement Category production binding v1

`PHIL-GEN-CATEGORY-001` is production-bound to the exact Rocq-extracted `GenericRequirementCategoryKernel.hs` staged by PR #624.

## Exact kernel identity

- staging exact green head: `6bc11d2d11395206250d089ee5959b9939fe66bc`
- staging merge: `13d5f95a305c7529ca2e00b41f21e4b0927e3427`
- staging run: `33743410032`
- staging artifact: `9888874108`
- artifact digest: `sha256:4ec62f952a29b012fad2bab58585c0d522c0022c1eb452979937018198a13940`
- exact kernel SHA-256: `f1b71633c1f312a9c0226f1f095b17b24475630213ce787c5b08cc4233b96b11`

The generated and source-tree kernel copies are byte-identical and the production workflow regenerates them from Rocq before testing the Haskell binding.

## Extracted semantic ownership

The exact kernel owns:

1. the thirteen-way requirement-category to competent-checker mapping;
2. final per-handoff semantic classification from reflected exactness facts, with fail-closed precedence for key, category, target, checked key, checked category, checked semantic form, and checked competence;
3. final exact interface-domain acceptance for public-requirement/handoff and public-requirement/checked-result domains.

Production `Phil.Core.Generic.RequirementCategory` routes its successful mapping, handoff classification, and domain acceptance through these extracted decisions. An impossible disagreement becomes `GenericRequirementCategoryKernelDisagreement`; handwritten code may therefore reject more aggressively on disagreement but cannot override an extracted rejection into success.

## Native boundary retained

The following remain native and explicit correspondence/predecessor boundaries:

- `Text`, `SemanticForm`, requirement-key, category, and competence representation/equality;
- list-to-`Map` normalization and duplicate detection;
- finite `Map`/`Set` domain construction, difference ordering, and traversal;
- construction of checked Haskell values;
- exact native diagnostics and payloads;
- source-to-generic-requirement elaboration;
- truth/competence of each category-specific downstream checker or assurance boundary;
- GHC/runtime correctness and the Rocq extraction toolchain.

## Closeout gate

The production gate:

- freshly compiles the Certified and implementation Rocq files;
- freshly extracts the kernel and requires SHA-256 `f1b71633c1f312a9c0226f1f095b17b24475630213ce787c5b08cc4233b96b11`;
- byte-compares both checked-in kernel copies;
- strictly typechecks the kernel, bridge, production checker, direct correspondence harness, production-binding harness, and unchanged GEN-014 corpus;
- executes all twenty-four direct extracted-kernel controls;
- executes nine production-binding controls;
- reruns the unchanged six-case GEN-014 corpus.

A fully green merge promotes `PHIL-GEN-CATEGORY-001` from `Discharged / Certified` to `Discharged / Implementation Refined`.
