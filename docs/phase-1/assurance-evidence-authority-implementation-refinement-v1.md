# Assurance evidence-authority implementation refinement v1

This tranche stages mechanical implementation refinement for `PHIL-ASSURE-EVID-001` without changing production `Phil.Assurance.Verify`.

The existing Certified model in `proof/Phil/Assurance/EvidenceUse.v` already defines executable authority gates for the two evidence families owned by this obligation:

- artifact-backed evidence: declared artifact, exact artifact identity, and trusted-availability digest match;
- `RuntimeEnforced` evidence: runtime mechanism present, mechanism complete, runtime residue present, cost reference present, and cost reference known.

`EvidenceAuthorityImplementation.v` exposes flat Boolean wrappers around those exact Certified definitions and proves that their extracted acceptance bit is exactly the corresponding conjunction of reflected facts. No new semantic model or alternate acceptance rule is introduced.

## Staging boundary

This tranche deliberately leaves production Haskell untouched. The extracted `AssuranceEvidenceAuthorityKernel.hs` is exercised directly, then the unchanged `Phil.Assurance.Verify` and 23-case `test/AssuranceMain.hs` corpus are typechecked and rerun.

A green staging merge therefore leaves the obligation at `Discharged / Certified`. Promotion to `Implementation Refined` requires a separate production-binding tranche that makes artifact-backed and `RuntimeEnforced` success depend on the exact extracted kernel.

## Explicit native/predecessor boundaries

The following remain native or predecessor facts supplied to the certified decision surface:

- concrete `AssuranceKind`, evidence-entry, artifact, runtime-mechanism, and cost-reference representation;
- artifact lookup, artifact reference equality, digest equality, and trusted-availability map correctness;
- runtime mechanism presence/construction and the truth of `runtimeComplete`;
- nonempty runtime residue and cost-reference enumeration;
- membership of every selected cost reference in the verification context's known-cost set;
- validation of runtime implementation artifacts;
- manifest selection, validity scope, evidence dependencies, assumptions, acceptance-rule closure, and assurance-use checks outside this narrow gate;
- exact diagnostic payload construction and native diagnostic ordering;
- truth/soundness of external proof, certificate, translation, test, runtime, and cost evidence;
- Rocq extraction/toolchain correctness and GHC/runtime correctness.

`Assumed` evidence is not part of this refinement slice. Its authority depends on the separate explicit-assumption boundary already modeled in `EvidenceUse.v`.

No dedicated Phase 1 conformance-matrix case owns this foundational gate; its production behavior is exercised by the assurance corpus and downstream runtime-carrier/deployment obligations.
