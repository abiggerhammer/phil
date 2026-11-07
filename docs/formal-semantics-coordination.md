# Formal-semantics slice claims (FSEM lane)

**Status:** proposed repository coordination control; not a language semantics
authority or a substitute for MHB-ATC scheduling. The new controller must land
before it is available on `main`. Its PR guard should be configured as a
**required status check** in GitHub branch protection; until then the CI failure
is visible but not an absolute merge prohibition.

## Why

FSEM-01 PRs [#1626](https://github.com/abiggerhammer/phil/pull/1626)
(production borrow-state trace) and
[#1627](https://github.com/abiggerhammer/phil/pull/1627)
(Rocq conditional model) were opened from different work sessions on the same
issue, without shared ownership of the next slice. They were complementary,
but happened to touch the same documentation index and needed a later
reconciliation. The shared GitHub `abiggerhammer` identity cannot identify
the actual initiating session. No particular autonomous hamster is accused.

This protocol covers **new** `lane: formal-semantics` PRs. Existing #1627 is
explicitly grandfathered, since a claim cannot honestly predate a PR that
already exists. The one PR that installs the protocol itself is also exempt.

## Rule: one owner per FSEM family

Before starting a substantive new slice, every assistant, Work session,
autonomous worker, or human contributor must:

1. Read [tracking issue #1613](https://github.com/abiggerhammer/phil/issues/1613)
   and **all open** `lane: formal-semantics` PRs (not only their titles).
   Compare intended source/proof/docs files and next-step obligations.
2. Choose the **family-level** claim key, e.g. `fsem-01`, `fsem-02`.
   Do not invent fine-grained keys like `fsem-01-trace` and
   `fsem-01-proof` to evade exclusivity. One open PR or claimed family
   blocks another worker unless an explicit, reviewed split is agreed first.
3. Acquire its unique claim reference *before creating a work branch or PR*.
   The first atomic Git ref creation wins; an HTTP 422 collision is a real
   **hold**, not permission to retry with a new key.
4. Confirm the claim is recorded as a comment in #1613 and put the exact key
   in the PR description. Mark the PR `lane: formal-semantics`.
5. Revalidate the live claim/PR list before merging. Only the claimed branch
   may use the reservation; check exact-head CI, not stale green runs.

### Acquire / record

From a trusted checkout of `main`, with Python 3 and a GitHub token having
repository contents-write, issues-write, and pull-request-read permission:

~~~bash
export GH_TOKEN="$(gh auth token)"
python3 scripts/fsem_claim.py acquire \
  --slice fsem-01 \
  --branch formal-semantics/fsem01-owner-encoding \
  --actor "chat:formal-semantics"
~~~

The controller prepares a **new commit first** containing a JSON record at
`.fsem-claim.json` in a claim-only tree. It atomically creates
`refs/heads/coord/fsem-claims/fsem-01` pointing to that commit. GitHub
enforces unique ref creation: there can be only one winner for `fsem-01`.
No claim record is pushed into `main`. Its record contains the issue,
family, claimed PR branch, supplied actor label, base SHA and claim timestamp.

After the ref is acquired, the controller posts an audit comment to #1613
containing the **exact claim commit SHA**. A failed comment **does not**
release the ref; verification fails closed until recovered with:

~~~bash
python3 scripts/fsem_claim.py announce --slice fsem-01
~~~

The actor label is for human coordination, **not authentication**. Different
ChatGPT sessions using the same GitHub account cannot be distinguished
cryptographically by this mechanism. The GitHub ref and claim commit, not the
actor label or a mutable issue comment, arbitrate exclusivity.

### Open and verify the PR

The claimed PR must come from the **exact predeclared branch**, have label
`lane: formal-semantics` and contain this stand-alone body line:

~~~text
FSEM-Slice: fsem-01
~~~

Use `python3 scripts/fsem_claim.py verify --pr NUMBER` to check the
live PR, exact claim ref, machine record and matching #1613 comment.
Verification rejects missing claims, a claim created *after* the PR,
a different head branch, incompatible family, or competing open PRs.
A `Nothing`/unclassified claim is never guessed from prose.

[The PR guard workflow](../.github/workflows/fsem-claim-guard.yml)
runs deterministic offline tests and requires the exact claim for new
formal-semantics PRs. It checks out the **trusted base** controller for
verification, not new PR code. New PRs missing the marker or claim fail the
check, even when their build/test checks are green.

**Repository administrator step:** enable
`FSEM Slice Claim Guard / exact-claim-before-pr` as a required status check
in the branch ruleset for `main`. That setting is outside this PR; without
it, a privileged merger could ignore a red coordination check. The workflow
is an auditable guard, not a global lock for unrelated lanes.

### Release, abandonment, and recovery

- On close/merge of a claimed PR, the
  [trusted-base release workflow](../.github/workflows/fsem-claim-release.yml)
  checks the live *closed* PR, claim branch and its creation time, and
  deletes **only its matching claim ref**, then comments on #1613.
- If work is abandoned **before any PR is opened**, the recorded claimant
  may run `python3 scripts/fsem_claim.py abort --slice fsem-01 --actor "chat:formal-semantics"`.
  This refuses to release while a matching/ambiguous PR is still open.
- Failed, interrupted, or missing releases do not silently time out.
  The existing ref continues to block acquisition. If recovery needs
  repository-administrator intervention, inspect the exact ref, commit,
  issue audit and open PRs before an explicit manual deletion. Record the
  reason and released ref SHA in #1613. **Never force-replace a live claim.**
- A PR closed without merge also releases its claim after verification; a
  reopened PR requires **a fresh claim** and a new exact-head review.

This is **logical slice ownership**, not a GitHub Actions runner slot.
[MHB-ATC](mhb-atc.md) still owns its opt-in resource admission machinery.
No existing proof, audit or implementation hamster schedules are changed.

## Acceptance controls

Run the offline unit tests (including two contenders for one atomic ref,
unscoped PR fail-closed, stale closed-event exclusion, exact PR matching,
and abandoned claim recovery):

~~~bash
python3 -m py_compile scripts/fsem_claim.py scripts/test_fsem_claim.py
python3 scripts/test_fsem_claim.py
~~~

Only enable strict claim enforcement once the controller CI has passed and
the intended required-check branch rule has been set. Existing #1627 can
finish its already-open proof work without an invented retrospective claim.
