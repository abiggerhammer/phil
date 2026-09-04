# Deployment Authority implementation refinement v1

This slice stages implementation refinement for `PHIL-DEPLOY-AUTH-001` / DEP-006 without changing production authority semantics.

The Certified authority relation decomposes into four executable gates:

1. `decideDeploymentAuthorityPolicyAdmissibleByFacts` — four facts: policy well-formedness, exact selected deployment policy, planned claim, and qualified claim.
2. `decideDeploymentAuthorityGrantMatchesByFacts` — seven facts: exact authority-policy revision, qualification identity, claim, action, resource, qualification-bounded validity end, and content-derived grant identity.
3. `decideDeploymentAuthorityIssuedByFacts` — four facts: valid deployment qualification, admissible authority policy, matching narrow grant, and grant validity beginning at the explicit issuance observation.
4. `decideDeploymentAuthorityUsableByFacts` — four facts: valid deployment qualification, admissible authority policy, matching narrow grant, and current grant validity at use time.

`DeploymentAuthorityImplementation.v` proves each Boolean gate equivalent to the corresponding Certified record in `DeploymentAuthority.v`. The qualification predecessor is deliberately reflected as one semantic fact: the production-binding follow-up must compose the already implementation-refined `PHIL-DEPLOY-QUAL-001` gate rather than duplicating deployment-qualification semantics inside the authority bridge.

`DeploymentAuthorityImplementationExtraction.v` extracts the four decisions to `DeploymentAuthorityKernel.hs`. `DeploymentAuthorityDecisionCorrespondenceMain.hs` directly tests every gate's all-exact acceptance case and one-fact-at-a-time rejection, including explicit rejection when the qualification predecessor is invalid at issuance or use time.

## Retained native/correspondence boundaries

The proof model does not absorb concrete `Text`/`Map`/`Set` representation, finite enumeration, canonical hashing or collision resistance, grant-id serialization, the mapping from Haskell non-empty policy/action/resource checks to `authorityPolicyWellFormed`, diagnostic reconstruction and precedence, secret-store/HSM/TEE enforcement, provider/platform truth, freshness/revocation truth, Haskell `Integer` ↔ proof-model `nat`, extraction/toolchain correctness, or GHC/runtime correctness.

These remain explicit native, evidence, or TCB boundaries. The future production-binding slice must preserve existing diagnostic ordering and fail closed on native-success/kernel-reject disagreement.

## Ledger status

This is a staging slice only. `src/Phil/Assurance/DeploymentAuthority.hs` remains unchanged. A green merge therefore leaves `PHIL-DEPLOY-AUTH-001` at **Discharged / Certified**. Promotion to **Implementation Refined** requires a later exact-kernel production-binding closeout.
