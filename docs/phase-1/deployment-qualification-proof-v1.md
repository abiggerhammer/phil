# PHIL-DEPLOY-QUAL-001 — deployment qualification proof v1

This proof certifies the normalized semantic rule implemented by Matrix `DEP-003`–`DEP-005`.

A deployment claim closes only through an explicit qualification bound to the exact preselected deployment plan. The qualification preserves exact artifact, deployment-policy, topology-revision, and claim-set identity and is checked at an explicit verifier observation point rather than against ambient clock authority.

Every selected deployment domain must have one exact evidence binding. The selected evidence must refer to the same artifact, policy, and domain; be current at the verifier observation point; cover every claim assigned to that domain; and enclose the qualification's complete validity interval. Extra bindings for domains outside the selected topology are not admitted.

A composite topology additionally requires one explicit composition-evidence object. That evidence must preserve the complete selected domain set, complete link set, complete claim set, artifact, policy, and topology revision and must itself be current for the qualification's validity interval. Independent per-domain attestations cannot substitute for composition evidence.

The theorem therefore captures the core negative properties exercised by the implementation corpus: raw attestation without qualification cannot close a claim; stale qualification or evidence cannot qualify; a qualification cannot outlive its evidence; missing selected-domain evidence rejects; missing required claim coverage rejects; missing composition evidence rejects; and a composition object cannot silently describe a different topology.

The dedicated workflow recompiles `proof/Phil/Assurance/DeploymentQualification.v` under Rocq 9.2.0, strictly typechecks the production deployment-qualification implementation and unchanged focused corpus, and reruns all ten `DEP-003`–`DEP-005` cases.

## Boundary

This is a semantic qualification theorem. Concrete Haskell `Text`/`Map`/`Set` representation, canonical hash construction, finite registry enumeration, exact diagnostic payload recovery, attestation cryptography, platform roots of trust, wall-clock truth, physical topology truth, and Rocq/GHC/toolchain correctness remain explicit correspondence/evidence/TCB boundaries.
