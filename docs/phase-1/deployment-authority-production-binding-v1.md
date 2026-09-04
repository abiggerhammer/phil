# Phase 1 Deployment Authority production binding v1

This closeout binds `PHIL-DEPLOY-AUTH-001` / DEP-006 production certification to the exact Rocq-extracted `DeploymentAuthorityKernel.hs` staged by #660.

## Exact kernel identity

The production branch checks in byte-identical copies at:

- `generated/DeploymentAuthorityKernel.hs`
- `src/DeploymentAuthorityKernel.hs`

Their required SHA-256 is:

`f47b41f780eb6f4123b8fce7d996b35f2394bcda3e03adba9003504b6d668bad`

The production-binding workflow freshly recompiles the Certified Deployment Qualification and Deployment Authority models, recompiles the Authority implementation correspondence, re-extracts `DeploymentAuthorityKernel.hs`, verifies that SHA-256, and byte-compares both checked-in copies before Haskell certification tests may run.

## Production certification path

`Phil.Assurance.DeploymentAuthorityCertification` preserves the existing detailed native Authority implementation as the first validator. Issuance first calls `issueDeploymentAuthority`; use-time validation first calls `checkDeploymentAuthorityGrant`. Therefore all existing native rejection ordering and diagnostic payloads remain unchanged.

Only a native success reaches the certified gates. The wrapper then calls `verifyDeploymentQualificationCertification`, not merely the legacy qualification checker, so DEP-006 composes the already implementation-refined `PHIL-DEPLOY-QUAL-001` predecessor boundary.

The Authority wrapper reflects the Certified model in four explicit families:

1. **Policy admissibility (4 facts)** — policy well-formedness, exact deployment-policy identity, planned claim, qualified claim.
2. **Grant matching (7 facts)** — exact authority-policy revision, qualification identity, claim, action, resource, qualification-bounded validity end, and content-derived grant identity.
3. **Issuance (4 facts)** — certified current qualification, accepted policy, accepted grant match, and grant begin equal to the issuance observation.
4. **Use-time validity (4 facts)** — certified current qualification, accepted policy, accepted grant match, and current grant interval.

Each family is passed to its exact extracted classifier. Any native-success/kernel-reject disagreement fails closed with the reflected facts preserved in `DeploymentAuthorityCertificationError`.

## Correspondence boundaries retained

The production binding does not claim proof of concrete `Text`/`Map`/`Set` representation, finite enumeration, canonical hashing or collision resistance, grant-id serialization, diagnostic reconstruction, Haskell `Integer` correspondence to the proof model's `nat`, secret-store/HSM/TEE enforcement, provider/platform truth, wall-clock or revocation truth, GHC/runtime correctness, or Rocq extraction/toolchain correctness.

The proof model has one `authorityPolicyWellFormed` Boolean. The Haskell bridge reflects that fact as the conjunction of the native non-empty policy revision, action, and resource requirements; this mapping remains an explicit correspondence boundary.

## Closeout criterion

`PHIL-DEPLOY-AUTH-001` may promote from **Certified** to **Implementation Refined** only when every workflow registered on the exact production-binding PR head is green and the dedicated production-binding workflow has:

- freshly re-extracted and byte-compared the exact kernel;
- passed strict Haskell typechecking;
- passed the direct extracted-kernel controls from #660;
- passed production certification controls including forced fail-closed disagreements and native-diagnostic precedence;
- rerun the implementation-refined DEP-003–005 predecessor corpus; and
- rerun the unchanged DEP-006 authority corpus.
