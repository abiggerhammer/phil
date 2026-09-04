# Deployment Qualification production binding v1

This closeout binds `PHIL-DEPLOY-QUAL-001` to the exact Rocq-extracted `DeploymentQualificationKernel.hs` staged by #654.

## Exact kernel

The production branch checks in the same extracted file at both:

- `generated/DeploymentQualificationKernel.hs`
- `src/DeploymentQualificationKernel.hs`

Its required SHA-256 is:

`31ebad6b671e91bc4225b95df6fba66e8a2723be3864da6fbf26423a6cd2107a`

The production-binding workflow freshly recompiles the Certified relation and implementation correspondence under Rocq 9.2.0, re-extracts the kernel, verifies that digest, and byte-compares both checked-in copies.

## Production composition

`Phil.Assurance.DeploymentQualificationCertification` keeps `checkDeploymentQualification` as the detailed native validator. A certification attempt first runs that validator unchanged, preserving its error ordering and diagnostic payloads. Only a native success reaches the kernel gate.

The wrapper then independently reflects the exact thirteen semantic facts used by `DeploymentQualificationValid` from the selected plan, qualification, domain evidence registry, composition evidence registry, and explicit observation point:

1. topology identity is exact;
2. every link names selected domains;
3. every selected claim has a selected domain;
4. every claim/domain assignment is sound;
5. artifact identity is exact;
6. policy identity is exact;
7. topology revision is exact;
8. covered claim set is exact;
9. qualification identity is exact;
10. qualification is current at the explicit observation point;
11. every selected domain has exact, current, interval-covering evidence for its assigned claims;
12. no evidence binding names an unselected domain;
13. composite topology evidence is exact and complete, or absent for a non-composite topology.

Those facts are passed to `decideDeploymentQualificationByFacts`. The successful path also passes qualification presence plus that decision to `decideDeploymentQualificationAvailableByFacts`. Any native-success/kernel-reject disagreement fails closed as `DeploymentQualificationCertificationKernelDisagreement`.

The wrapper intentionally does not fold extra Haskell-only representation checks into the thirteen reflected facts. Evidence registry key self-identity, concrete `Text`/`Map`/`Set` representation, canonical hashing/collision resistance, finite enumeration, `Integer` ↔ proof-model `nat` correspondence, diagnostic reconstruction, attestation/platform/clock/topology truth, and extraction/compiler/runtime correctness remain explicit native, evidence, correspondence, or TCB boundaries.

## Regression gate

The dedicated production-binding workflow:

- freshly re-extracts and byte-compares the exact kernel;
- strictly typechecks the native checker, certification wrapper, both checked-in kernel copies, direct extracted-kernel harness, production-binding harness, and unchanged DEP-003–005 corpus;
- reruns the direct extracted-kernel controls from #654;
- verifies a valid composite production qualification reflects all thirteen facts and is kernel accepted;
- forces one reflected fact false and confirms fail-closed disagreement;
- forces qualification presence false and confirms the availability gate rejects;
- confirms native diagnostic precedence is preserved;
- reruns the unchanged DEP-003–005 corpus.

A green exact-head merge closes the production-binding step and permits `PHIL-DEPLOY-QUAL-001` to move from **Certified** to **Implementation Refined**.
