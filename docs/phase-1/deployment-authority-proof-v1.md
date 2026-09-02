# PHIL-DEPLOY-AUTH-001 — deployment authority proof v1

This proof certifies Matrix `DEP-006` on top of Certified `PHIL-DEPLOY-QUAL-001`.

A valid deployment qualification is necessary but never sufficient to create ambient authority. Authority issuance additionally requires one explicit well-formed authority policy naming the exact selected deployment-policy revision, one claim already present in both the deployment plan and current qualification, one exact action, and one exact resource.

The resulting grant remains bound to the authority-policy revision, qualification identity, claim, action, resource, issuance observation, qualification validity end, and its content identity. A grant cannot outlive the qualification that justified it.

Use-time validation re-establishes the qualification at the current verifier observation point and rechecks the same narrow policy/grant correspondence. A changed action or resource therefore cannot remain usable, and a qualification that becomes stale invalidates authority that was valid when originally issued.

The proof composes `PHIL-DEPLOY-QUAL-001` rather than duplicating deployment qualification. Its dedicated workflow recompiles that predecessor and this proof under Rocq 9.2.0, strictly typechecks the production qualification/authority implementations and unchanged corpora under `-Wall -Werror`, reruns all ten DEP-003–005 qualification cases, and reruns all seven DEP-006 authority cases.

## Boundary

This is a semantic authority theorem. Concrete Haskell `Text`/`Map`/`Set` representation, canonical hash construction, exact diagnostic payload recovery, secret-store/HSM/TEE enforcement correctness, revocation/freshness truth, external platform evidence, and Rocq/GHC/toolchain correctness remain explicit correspondence/evidence/TCB boundaries.
