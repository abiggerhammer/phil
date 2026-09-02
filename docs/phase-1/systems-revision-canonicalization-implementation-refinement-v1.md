# PHIL-SYS-REV-001 implementation refinement staging

`PHIL-SYS-REV-001` is already Certified by PR #504. This tranche stages an executable, representation-neutral construction surface without changing production behavior.

## Extracted construction plans

`SystemsRevisionCanonicalizationImplementation.v` follows the same construction-plan pattern already used for architecture revision refinement. The plan fields are polymorphic: Rocq owns which semantic coordinates participate in each revision and which namespace is selected, while native Haskell remains responsible for realizing those coordinates into the existing canonical representation.

### SystemsArtifactRevision

`planSystemsArtifactRevision` carries exactly:

- source semantics;
- Systems-program semantics;
- StageContract semantics; and
- lowering semantics.

Source formatting, diagnostic presentation, container ordering, and backend symbol spelling are absent from the plan, matching the Certified theorem's nonsemantic projection.

### Phase1StageContractRevision

`planPhase1StageContractRevision` carries exactly:

- ArchitectureInstance identity;
- realization identity;
- SystemsArtifactRevision;
- verifier-profile revision;
- source facts;
- dispositions;
- Systems mechanisms; and
- justifications.

The corresponding implementation theorems prove that both extracted plans coincide field-for-field with the Certified abstract canonical revisions and remain invariant when only the theorem's nonsemantic metadata coordinates vary.

## Representation boundary

This staging deliberately does **not** claim that Rocq serializes or hashes the concrete production values. The following remain explicit ADR-019/native correspondence boundaries:

- `SystemsArtifact` normalization into the semantic coordinates represented by the Systems plan;
- native `Text`, `Map`, `Set`, list, IR, StageContract, and lowering-ledger representation;
- exact mapping from extracted namespace/plan coordinates to canonical `SemanticForm` field names;
- `canonicalSemanticForm` concrete encoding;
- `systemsArtifactDigest` and SHA-256 construction;
- collision resistance/injectivity of the concrete serializer/hash composition; and
- GHC/Rocq extraction/runtime correctness.

Production `src/Phil/Systems/Phase1Stage.hs` is unchanged in this staging PR. A separate closeout must check in the exact extracted construction kernel and route `deriveSystemsArtifactRevision` and `derivePhase1StageContractRevision` through its construction plans before the ledger may move from `Discharged / Certified` to `Discharged / Implementation Refined`.

## Staging verification

The existing `Phase 1 Systems Revision Canonicalization Proofs` workflow is extended to:

- compile the Certified theorem plus implementation-correspondence theorem;
- fresh-extract `SystemsRevisionCanonicalizationKernel.hs` under Rocq 9.2;
- strict-typecheck and execute direct construction-plan controls;
- strict-typecheck the unchanged production revision implementation;
- rerun the unchanged generic Systems-stage and final StageClosure canonicalization corpora; and
- record proof, extraction, production, corpus, harness, and staging-document identities.
