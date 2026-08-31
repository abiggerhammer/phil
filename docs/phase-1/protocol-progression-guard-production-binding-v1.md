# PHIL-PROT-STEP-001 production binding v1

This closes the bounded implementation-refinement correspondence for the already-Certified protocol progression / guarded-transition obligation.

## Exact extracted kernel

Production checks in `src/ProtocolProgressionGuardKernel.hs`, byte-for-byte from the successful #456 extraction.

SHA-256:

`4378dfae72309f262db9188f8e12c9f4efb568f796f8677324d646c94fd63e63`

The production workflow fresh-extracts the kernel from Rocq, byte-compares it to the checked-in file, and asserts this hash before running Haskell correspondence checks.

## Bound production choices

`src/Phil/Core/Protocol.hs` retains native endpoint-map lookup, concrete resource/session execution, and exact diagnostics. After the existing exact protocol-identity and Session checks succeed, it reflects:

1. predecessor metadata liveness;
2. successor occurrence distinctness;
3. successor metadata freshness; and
4. close predecessor liveness

into the extracted progression decisions. Accepted continuation reconstructs the exact successor protocol instance, role, and successor Session through `planProtocolSuccessorContract`; close installs no successor.

`src/Phil/Assurance/ProtocolGuard.hs` still verifies the complete assurance package through `verifyManifest`. During ordered guard traversal it reflects native `Set.member` duplicate facts into `decideProtocolGuardListByFact`, and for each exact required revision reflects manifest presence and certification-scope membership into `decideProtocolGuardRequirementByFacts`.

Thus branch labels and transition names still supply no proof authority, duplicate requirements still reject in traversal order, missing revision precedes uncertified revision, and successful guarded progression still delegates structural action legality to the already-refined protocol identity/session path.

## Preserved native/predecessor boundaries

This closeout does not move these responsibilities into the extracted kernel:

- concrete Haskell `Name`, `ProtocolInstanceRevision`, `ProtocolRoleKey`, `Session`, `RevisionId`, `Map`, and `Set` representation/equality;
- endpoint-map and resource-context lookup/mutation;
- Session action legality and exact linear resource transition;
- exact protocol instance/role/current-session action gating already owned by `ProtocolIdentityKernel` and the Session checker;
- assurance manifest/evidence verification, evidence truth/competence, validity scope, and certification truth;
- diagnostic payload construction;
- GHC, Rocq extraction, runtime, target serialization/ABI/wire behavior, and transport correctness.

## Closeout criterion

`PHIL-PROT-STEP-001` may move from **Discharged / Certified** to **Discharged / Implementation Refined** only after an exact-head run:

- recompiles the Certified theorem and implementation correspondence;
- fresh-extracts the kernel and byte-compares it to production;
- asserts the harvested kernel SHA-256;
- strict-typechecks the checked-in kernel and bound production paths;
- executes the direct kernel controls against the production kernel; and
- reruns the unchanged PROT-005 stale-endpoint and PROT-006 guarded-transition pressure corpora.
