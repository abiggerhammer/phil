# Systems control preservation production binding v1

This closes the implementation-refinement binding for `PHIL-SYS-CONTROL-001` after staging in PR #507.

The exact Rocq-extracted `SystemsControlPreservationKernel.hs` is checked in at `src/SystemsControlPreservationKernel.hs` with SHA-256 `c85d50d0e2e8e9c694729509829d3e5bab9361fcbc399f0d1626cbfb4743c042`.

Production keeps concrete Haskell representation work explicit: canonical revision construction, `Text`/key/revision equality, `Map`/`Set`/list/CFG traversal, block/operation/value lookup, branch/release enumeration, subject lookup, endpoint-lineage construction, runtime/protocol evidence construction, and exact diagnostic payloads remain native correspondence boundaries.

The normalized semantic decisions are kernel-owned:

- SYS-007 routes exact branch outcome-domain, owner-fate-domain, owner-fate realization, control-class, and tracked-owning-value gates through `decideBranchPreservationByFacts`; native code retains exact owner/release/control payload recovery.
- SYS-008 routes projection-kind and slot-domain checks, restricted-owner modes, fixed-subject admission, restricted-owner uniqueness, linear-owner coverage, scoped-loan exclusion, and restricted closure-carrier cardinality/sharing through `decideStateProjectionByFacts`.
- SYS-009 routes checked-vs-runtime protocol basis, operation/terminator semantic target admission, exact transport use, outcome-domain equality, instance/role preservation, successor freshness, exactly-once predecessor consumption/successor production, and acyclic lineage through `decideProtocolPreservationByFacts`.
- SYS-010 routes boundary transport/owner/subject/length correspondence, runtime kind and revision/evidence, protocol-transition correspondence, successor-producing commit, terminal failure, and the final complete-before-success acceptance through `decideBoundaryCommitByFacts`; source-fact/value/runtime-site construction and lookup stay native.
- successful SYS-007--010 production verification is finally reflected through `decideSystemsControlByFacts`, preserving the Certified predecessor order.

The closeout workflow fresh-extracts under Rocq 9.2, requires the staged SHA-256 and byte-for-byte equality with the checked-in kernel, strict-typechecks the bound production chain, executes all 44 direct extracted-kernel controls, and reruns the unchanged 46-case SYS-007--010 correspondence corpus.
