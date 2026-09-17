# Verification evidence reuse proof boundary v1

This note records the normative certification boundary for `PHIL-VERIFY-REUSE-001`, corresponding to the VER-006 reusable proof-evidence implementation in `Phil.Verification.ProofEvidence`.

## Certified reuse relation

A checked proof artifact may be prepared for later reuse only against the exact obligation-graph revision in which that artifact was accepted. Preparation captures the exact target obligation revision, the target's exact direct dependency-revision set, and the explicitly declared ADR-010 validity scope.

After preparation, whole-graph identity is deliberately **not** a reuse key. Reuse succeeds exactly when:

1. the cached target revision is still present;
2. that exact target revision remains in certification scope;
3. the target's direct dependency-revision set is extensionally identical to the captured set; and
4. every validity dimension bound by the cached evidence still has the exact expected value in the current effective validity context.

This gives the intended non-overinvalidation rule: unrelated graph edits and extra unbound context dimensions do not invalidate independently scoped evidence.

## Certified invalidation cases

The semantic proof establishes that reuse cannot survive:

- removal/replacement of the exact target revision;
- removal of that target from certification scope;
- any change to the exact direct dependency-revision set; or
- any changed or missing value for a validity dimension bound by the cached evidence.

The proof imports `PHIL-ASSURE-VALIDITY-001` rather than defining another validity model. In particular, exact DefinitionRevision, qualification revision, checker/profile, target, or other dimensions invalidate reuse only when the accepted evidence actually bound those dimensions.

## Generic conditional assurance composition

The proof also composes the now-Certified `PHIL-ASSURE-GENERIC-001` boundary. Reusable proof evidence and reusable generic-body assurance remain separate authorities: a current application may retain the exact previously certified generic body while independently requiring the cached proof evidence to remain valid under its own target/dependency/validity coordinates. No application identity, evidence replacement, or backend realization silently rekeys the generic body.

## Executable correspondence

`VerificationReuseImplementation.v` mirrors the acceptance surface of `evaluateReusableProofEvidence` over reflected native facts:

- target present;
- target in certification scope;
- direct dependency set exactly equal; and
- one Boolean lookup/equality fact for every bound validity-scope entry.

Under complete validity-scope enumeration and faithful fact reflection, the finite decision accepts **iff** the certified semantic reuse relation holds.

The Haskell implementation retains richer `EvidenceReuseStaleness` diagnostics. Their concrete `Map.toAscList` ordering and payload construction remain a native diagnostic boundary; they do not grant reuse authority.

## Representation and predecessor boundary

This certification does not prove concrete `Digest`, `RevisionId`, `Text`, `Data.Map`, or `Data.Set` implementations, canonical graph revision hashing, obligation-revision construction, proof-certificate truth, or the truth of external validity dimensions. Those remain representation, checker, or predecessor assurance boundaries.

Likewise, preparation's nonempty validity-dimension syntax check remains a concrete representation admission check. The theorem owns the semantic effect of the admitted normalized scope, not Text syntax.

## Regression binding

The dedicated `Phase 1 Verification Reuse Proofs` workflow recompiles the validity-scope and generic-assurance predecessors, checks the new semantic and executable correspondence proofs, rebuilds the complete Haskell substrate, strict-typechecks `Phil.Verification.ProofEvidence` and the unchanged VER-006 regression harness, replays that harness, and reruns the generic-assurance predecessor corpus and assurance tests.

Merge criterion: every workflow registered on the exact PR head must complete successfully.
