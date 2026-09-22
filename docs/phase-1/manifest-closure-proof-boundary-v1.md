# PHIL-P1-MANIFEST-001 proof boundary

This slice certifies witness-neutral source assurance closure from an exact
VerificationBundle into an AssuranceManifest.

It owns exact policy and architecture binding, exact obligation-domain closure,
current accepted evidence, exact target revision, explicit assumption
dependencies, no unused selected assumptions, explicit permitted exports,
validity-scope matching, and fail-closed rejection of evidence absent from the
current bundle or ledger.

It composes PHIL-VERIFY-WORKFLOW-001, PHIL-ASSURE-GENERIC-001,
PHIL-PROV-LINEAGE-001, PHIL-ASSURE-SCOPE-001, and ADR-010. Final emitted-artifact
certification remains downstream in PHIL-VERIFY-ARTIFACT-001.

Concrete Text/Digest/Map/Set representation, SHA-256, manifest-id construction,
external/provider evidence truth, and Haskell/Rocq toolchain correctness remain
explicit boundaries.


## Selected-evidence membership correspondence

The production INT-002 closure path now enumerates the exact
`manifestClosureEvidence` selection and requires every selected key to occur
in `verificationBundleAcceptedEvidence`. The bundle-reference traversal still
performs the concrete ID/digest/target-revision/accepted-ledger checks for every
listed reference.

`ManifestClosureImplementation.v` reflects that traversal with:

- a complete enumeration of the selected evidence domain;
- a reflected native bundle-membership predicate;
- a finite `forallb` membership decision over the selected domain; and
- a theorem upgrading evidence validity with every other semantic premise into
  `P1EvidenceValidFor`, including the current-bundle membership premise.

Static and runtime disposition corollaries use the same correspondence. The
negative controls cover an empty bundle and a distinct selected key absent from
a nonempty bundle; positive controls retain subset selection from a larger
bundle. Extra unselected ledger evidence remains outside this membership
obligation.

This closes the quantifier-direction gap identified by
`PHIL-AUD-MANIFEST-EVIDENCE-MEMBERSHIP-001`: the proof ranges over selected
evidence, not merely over references already present in the bundle. Concrete
Map/Set enumeration and membership, exact reference serialization/digests, and
the final manifest verifier's assurance-use traversal remain explicit native
correspondence boundaries.
