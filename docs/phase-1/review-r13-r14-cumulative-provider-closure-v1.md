# R13/R14-C1: independent provider authority reaches cumulative closure

## Scope and predecessor

This slice addresses R13/R14-C1 in the 20 September 2026 audit continuation at
`2b0e9982240b4b8d9a1a7a24cc4850be4cb5d331`. It follows PR #1244, merged at
`6e31ffc81aeb284967e4238fafe5222618dc423a`, which repaired R19's qualified
implementation-entry equality. All 25 PR #1244 workflows succeeded at head
`58e60e6c2d115c2d02bb9b3ebeddb8e9c61b1e0b`, including the 11-case R19 corpus,
its strict typecheck, and the existing R13/R14/provider controls.

The audited gap was not in the strong local provider check alone. The public
StageClosure verifier reached a relative authority/effect check through
BranchResource, so coordinated deletion of a site, link and use could survive
final closure even with every candidate revision recomputed.

## Mandatory checked authority

`ProviderCallClosureAuthority` is an opaque data type in
`Phil.Systems.BranchResourceFailure`. Its constructor is private, it has no
exported record fields, and it is not a public newtype coercion or Read surface.
`certifyProviderCallClosureAuthority` is the only ordinary constructor. It
requires the independent expectation map and runs
`verifyAuthorityEffectStageBundleAgainst` before retaining that map and the
complete verified Subject/Systems source value.

Both production witness materializers pass the existing separately declared
`steveProviderCallExpectations` or `uploadProviderCallExpectations`. They do not
reconstruct expectations from candidate links, selected admissions, runtime
symbols, or the records that survived a mutation.

`makeBranchResourceStageBundle` now requires this authority explicitly, in
addition to the candidate authority/effect stage and branch contracts. The
public branch verifier unconditionally:

1. Compares the complete current SubjectStageBundle with the authority's source,
   rather than accepting equality of claimed revision strings alone.
2. Reruns the strong authority/effect verifier using the immutable independent
   expectation map retained by the authority. This includes exact provider-call
   coverage, independent operation correspondence, and the R19 entry check.
3. Performs the existing branch revision, outcome, ownership and control checks.

The candidate remains editable for translation validation. A previously
accepted token is not treated as blanket approval of a changed candidate.
There is no optional Against-only branch path and no empty-map fallback.
The lower relative provider and authority/effect APIs remain available for
explicit relative analyses, but cannot substitute for this mandatory gate.

## Both cumulative routes

The existing public `verifyStageClosureBundle` reaches the new gate on both
alternatives without changing its calling convention:

- `ConcreteThroughBranch` -> BranchResource -> strong authority/effect.
- `ConcreteThroughBoundary` -> BoundaryCommit -> ProtocolState -> ControlState
  -> BranchResource -> strong authority/effect.

The verification/certification consumers that invoke the existing final
StageClosure verifier therefore inherit the mandatory gate; no separate helper
call must be remembered at each caller. This slice does not claim an audit of
every consumer outside that API.

## Identity and trust boundary

The sealed context has a domain-separated SHA-256 identity over canonical
source revision plus the entire independent site/occurrence/operation map.
The complete source value is also retained for exact origin comparison.
The digest accessor is not itself authority and cannot construct a token.

The BranchResource canonical format advances to v2 and includes this context
identity. Existing cumulative constructors carry that revision through both
routes into ClosedStageContractRevision. Old context-free branch values must
be rebuilt; they are not silently upgraded or admitted under v1 identity.

The source-to-expectation producer remains a trusted input at issuance. This
is an implementation of the audit's opaque-checked-authority option, not a
proof that any arbitrary caller-supplied map describes all source calls.
Explicitly choosing a different independently supplied inventory is a new
context selection with a different bound identity, not an in-place edit of an
existing token. No claim is made that Haskell opacity authenticates arbitrary
external producers, unsafe coercions, or manufactured proof records.

## Regression corpus

`test/Phase1ReviewC1CumulativeProviderClosureMain.hs` contains fourteen cases:

- Unchanged Steve through BranchResource and Upload through BoundaryCommit.
- Authority-construction rejection and direct BranchResource rejection of
  coordinated provider site/link/use omission.
- Final Steve rejection of single-site omission and complete erasure, and
  final Upload rejection of provider-call erasure through all boundary layers.
- Final rejection of a wrong genuine operation (R13) and coordinated selected
  entry/link rebinding with genuine qualification unchanged (R19).
- Cross-source authority substitution in both directions, using only genuine
  tokens from accepted fixtures.
- Determinism under expectation map reordering, exact restoration of the
  original closure, and retention of the context identity in both final
  canonical representations.

Omission controls retain acceptance by the relative authority/effect checker
and require the exact independent-inventory diagnostic from the final public
consumer. Candidate mutations preserve source, next-stage branch, sealed
expectations and branch contracts. Provider, authority/effect, branch and all
control/protocol/boundary/final revisions are rebuilt and freshness-checked.
Donor-token tests change only authority selection and its dependent identities;
they require the specific source-origin mismatch. The tests do not pass merely
because a stale hash or an unrelated gate rejected a malformed fixture.

## CI and proof handoff

The existing Phase 1 Review R14 Provider Call Inventory workflow now includes
strict typechecking and execution of the cumulative corpus, plus the existing
branch and StageClosure controls. Its R19, R14, R13 and provider/authority
regressions remain. Path filters cover the cumulative production chain and
new corpus. There is no additional workflow or Cabal component.

At authoring, the implementation and corpus are submitted for CI. GHC and
Cabal were not available locally, so no local Haskell execution or successful
new regression run is claimed. Exact-head CI and independent audit re-review
are required before closeout.

No Rocq source, generated kernel or Certified-ledger status is changed. The
new opaque-authority admission, origin comparison, context identity and
mandatory cumulative composition need their own proof/refinement closeout;
the prior normalized control/closure theorems are not relabeled as proving
these new concrete checks. R1, R10/R16 and R17/R18 remain separate repairs.
