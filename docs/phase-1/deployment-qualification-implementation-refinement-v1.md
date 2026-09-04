# Deployment Qualification implementation refinement v1

`PHIL-DEPLOY-QUAL-001` is Certified by `proof/Phil/Assurance/DeploymentQualification.v`. This staging slice adds a representation-neutral executable correspondence layer without changing the production `Phil.Assurance.DeploymentQualification` checker.

## Extracted decision surface

`proof/Phil/Assurance/DeploymentQualificationImplementation.v` proves an executable Boolean classifier equivalent to the exact Certified `DeploymentQualificationValid` record when each reflected fact denotes its stated semantic proposition. The final extracted conjunction requires all of the following:

- valid topology identity and well-formed links;
- total and sound claim-to-domain assignment;
- exact artifact, deployment policy, topology revision, and covered-claim set;
- valid qualification identity and current qualification interval;
- exact evidence for every selected domain, with no extra domain binding;
- the Certified simple/composite topology evidence requirement.

A second extracted classifier proves that qualification presence plus validity is equivalent to `DeploymentQualificationAvailable`. This preserves the Certified rule that raw attestation or verifier output without a qualification cannot close a deployment-dependent claim.

The extraction driver emits `DeploymentQualificationKernel.hs`. Staging CI invokes that exact generated module directly, rejects each missing semantic fact independently, and reruns the unchanged DEP-003 through DEP-005 corpus.

## Native correspondence boundaries retained

The following remain deliberately native and are not silently promoted into the extracted kernel:

- `Text`, `Map`, `Set`, `RevisionId`, artifact/policy/topology/evidence-key representation and equality;
- canonical topology and qualification hashing plus cryptographic collision resistance;
- complete finite enumeration of selected domains, links, claims, claim-domain assignments, and qualification evidence bindings;
- exact registry lookup, map-key identity, evidence-domain attribution, and missing-claim calculation;
- Haskell `Integer` to proof-model `nat` correspondence and concrete validity-interval arithmetic;
- attestation cryptography, platform roots of trust, wall-clock truth, and physical topology truth;
- detailed typed diagnostic ordering and payload construction;
- GHC/runtime behavior and Rocq extraction correctness.

Those native computations must reflect their exact semantic results into the Boolean inputs proved here. A later production-binding slice must check in the exact extracted kernel and route successful production qualification through it fail-closed before the ledger may move above `Discharged / Certified`.

A green staging PR therefore **does not** promote `PHIL-DEPLOY-QUAL-001` to `Implementation Refined`.
