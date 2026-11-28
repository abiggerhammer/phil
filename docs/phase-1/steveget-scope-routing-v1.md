# SteveGet scope routing v1

Both existing workflows continue to run their SteveGet regression jobs when
their branch and path filters select them. Scope is a separate job. Its existing
job ID and check name stay in place. The only new trigger paths are
`scripts/ci/steveget_scope_routing.py` and
`scripts/ci/test_steveget_scope_routing.py`, added to both existing push and PR
path lists in each workflow.

## Scope decisions

| Event | Outcome |
| --- | --- |
| Open, synchronized, or reopened PR with the profile's exact historical head, in `abiggerhammer/phil`, targeting `main` | APPLICABLE after the historical path predicate and live claim pass. |
| Coherent PR with any other head branch, including a coherent nonhistorical fork | N/A. Report owner review required if the comparison touches a direct legacy or routing path. |
| Nondeleted push to the exact profile branch ref, with a coherent event and checkout | APPLICABLE after the cumulative path predicate and live claim pass. |
| Historical head spelling from a fork or against another base branch, unsupported event, bad or contradictory identity, unavailable comparison, path refusal, or historical claim failure | REFUSE with a nonzero exit and a diagnostic. |

A PR uses the literal head branch for routing. Labels, the PR body, branch
substrings, changed paths, and claim availability supply no routing authority.
The helper checks the repository ID `1341890518` and name `abiggerhammer/phil`
across the runner and event, reconciles the PR head and base repositories and
refs, and checks a positive PR number and exact `refs/pull/<number>/merge` ref.
Historical push ref matching is exact and tags refuse. The actual full-history
scope checkout must equal `GITHUB_SHA`. A PR's synthetic merge must have exactly
two parents in event base/head order. Missing fork identity or malformed inputs
refuse.

A successful nonhistorical scope job emits:

> historical scope NOT APPLICABLE; historical predicate and claim not evaluated; no changed-file authorization or claim ownership supplied

The extra `owner-review-required` classification covers either legacy
workflow's code, proof, tests, documentation and workflow, plus the helper,
its tests and this document. A no-renames status comparison exposes deleted
paths and rename origins as well as destinations. Shared Cabal changes alone
do not trigger that classification. N/A leaves the independent claim guard
and regression outcomes in force.

## Comparison and historical authority

For a PR, the comparison uses the literal event base and head. For a push, it
resolves `refs/heads/main` once from the configured expected repository on
`origin`. If the selected object is unavailable locally, the helper fetches
that literal object ID. The result is a **run-selected main baseline**. Event
`before` and the claim's acquisition baseline do not select the cumulative diff.
For both events, the helper requires commit objects and one merge base, then
compares that merge base to the literal head or push `after`. It does not compare
the synthetic tree or re-read a moving ref during the comparison.

FSEM-05's branch is
`formal-semantics/fsem05-steveget-qualified-source-events`. Its path predicate
uses the original Git name-only comparison semantics and accepts a nonempty
subset of the original six paths, with `phil-core.cabal` included in the
allowlist. FSEM-06's branch is
`formal-semantics/fsem06-steveget-core-payload-refinement`. Its predicate
requires the original five unique additions, with status `A` for every record.
Cabal, modification, deletion, rename, copy, and extra or missing paths fail
that predicate. The new paths are excluded from both historical allowlists.
The helper passes arguments directly to Git and uses NUL framing. It refuses
unterminated, empty, missing, or malformed status fields instead of trying
another comparison.

Only on a historical route that passes its path predicate, the helper loads
the unchanged `scripts/fsem_claim.py` bytes at the trusted immutable PR base
or run-selected push baseline. It calls `live_claim` and
`require_issue_record` with read-only API access and verifies the exact family,
branch and actor. The actors are `hamster:fsem-05-source` and
`hamster:fsem-06-core`, respectively. A missing live ref, wrong claim,
matching release record, failed API read, or missing, multiple or mismatched
issue records refuses. A historical spelling supplies no authority to reuse
a consumed allocation.

The JSON receipt records the profile, event and validated repository
identities and refs, checked subject, workflow SHA and ref, selected
comparison SHAs, merge base, path/status evidence and decision. A successful
historical receipt alone includes the claim SHA. No token is recorded.
Scope receipts identify only the scope checkout. FSEM-05's GHC and Rocq jobs
retain the default PR merge checkout and remain independent. FSEM-06's
Rocq and GHC jobs retain exact-head PR checkouts, with GHC downstream of
Rocq and reading the same-run extracted artifact. Job failure, skip, and
pending remain distinct from success.

## Offline controls and bootstrap

Run `python3 scripts/ci/test_steveget_scope_routing.py` from the full checkout.
Both scope jobs run these standard-library controls before using the helper on
the actual event. They exercise the helper in temporary Git repositories and
the real pinned claim controller against fixture-only, read-only responses.
The controls cover historical PRs #2017 and #2039, altered paths and statuses,
claim and issue failures, exact D3 and REC-02B path fixtures, Cabal and
unrelated paths, direct legacy and repair paths, spoofed or malformed events,
forks, object and merge-base failures, and immutable PR and cumulative push
comparisons. The independent review packet also records the old predicates'
offline results, YAML and regression-body equivalence, and workflow privilege
checks. The old predicates reject the repair, D3 and REC-02B; those offline
results provide no waiver. REC-02B remains a preclaim STOP.

This offline candidate ends at the frozen handoff to independent Astra
implementation and bootstrap review. Any future live work requires a
separate owner allocation. The proposed bootstrap is one ordinary
`infra/steveget-scope-routing` PR to `main` with no FSEM lane, marker or claim.
GitHub's documented event selection and synthetic merge checkout imply
candidate-integrated PR definitions. That is an expectation to verify against
actual provider runs. Before a branch or PR, the owner must reconcile fresh
main, all-state PRs and path ownership, actual workflow selection and all
effective required contexts, including integration `15368` for
`exact-claim-before-pr`, MHB workflow audits, and the remaining classic
protection visibility gap (HTTP 403).

If separately authorized later, a draft should provide actual workflow/run/
attempt/job identities, workflow and helper blobs, event base/head/merge
base, scope and regression subjects, both explicit N/A plus owner-review
receipts, real regressions and MHB audits, the existing non-FSEM claim guard
result and every required check. If GitHub selects an applicable unchanged
definition or any required gate rejects, stop and preserve the draft. Do not
bypass a check, change policy, or reuse a historical claim. Require ordinary
protected exact-head approval and independently verified checks before merge.
Record the workflow-tree delta when reevaluating G2-1 applicability. The
historical #2024 review stays tied to its frozen subject.

After protected landing, D3 requires a separately authorized successor
under #2033, on the same claim and branch, with the six original nonworkflow
candidate blobs preserved, a revised manifest, fresh exact-head and
integration evidence, all checks and independent review. A stale rerun
cannot validate that successor. REC-02B requires a separate preclaim
preflight against the landed policy. Other holds and allocations remain in
force.

- [Architecture and exact patch contract](https://github.com/abiggerhammer/phil/issues/2050#issuecomment-7205535996)
- [Replacement conditions](https://github.com/abiggerhammer/phil/issues/2050#issuecomment-7225813827)
- [Offline replacement authorization](https://github.com/abiggerhammer/phil/issues/2050#issuecomment-7237390185)
- [GitHub workflow selection](https://docs.github.com/en/actions/concepts/workflows-and-actions/workflows)
- [GitHub event and checkout subjects](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows)
- [GitHub runner variables](https://docs.github.com/en/actions/reference/workflows-and-actions/variables)
