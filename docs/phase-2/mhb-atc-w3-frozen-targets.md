# W3 immutable frozen target trio — proposed source-only architecture

**STATUS: DORMANT CANDIDATE, NEW INDEPENDENT REVIEW REQUIRED.**
No publisher/worker token, protected-ref write, workflow dispatch in run or
cleanup mode, PR CREATE/REOPEN, source activation, or broker activation is
authorized by this proposal.

Tracking: [worker App confinement #1863](https://github.com/abiggerhammer/phil/issues/1863),
[immutable admitted-head commissioning #1839](https://github.com/abiggerhammer/phil/issues/1839),
[accepted W3 hardening #1948](https://github.com/abiggerhammer/phil/pull/1948),
[prior tree review #1951](https://github.com/abiggerhammer/phil/pull/1951).

## Why freeze immutable test commits

The old W3 design took the source, first parent and grandparent from the
**latest** owner/main manual workflow dispatch. Every unrelated hamster merge
that edited any workflow changed the candidate `.github/workflows` tree,
invalidated the pin, and restarted a three-commit stabilization period.
Re-pinning in another PR itself caused more full repository CI fanout.

The actual security objective is narrower and stronger: **every possible
protected-ref target commit must select an independently reviewed, safe
workflow tree**. Those targets need valid first-parent ancestry for the
CREATE/fast-forward/FORCE-UPDATE cases, but they need not be the three
latest commits of `main`.

### Reviewed historical objects proposed for selection

| Role | Immutable Git commit SHA |
|---|---|
| Frozen ref source (worker CREATE target / fast-forward UPDATE target) | `d82a60a3c9f448c2e59ebe7bdfc710109159f7a9` |
| Frozen first parent (publisher seed / canary target) | `e38814a2e916252a8a7f3dd438943e8f4a21664a` |
| Frozen grandparent (worker FORCE-UPDATE target) | `4b7594ed83648372171a9bb1c34647522c064b22` |

All three objects have the same **Git `.github/workflows` subtree SHA**:
`4b8b338a7a0ebed852407c9288d4a293bc26066f`.

The subtrees match the earlier **621-workflow tree** that Astra accepted
at #1951's original first-run review, before the later 622-workflow tree
became the accepted newer candidate. Reusing that tree as a W3 fixture
must be independently accepted **as part of this redesigned source contract**.
No claim is made that acceptance of either earlier pin alone establishes
the trust of the new frozen-target selection.

The frozen source commit's first parent is exactly the frozen first-parent
commit; that commit's first parent is exactly the frozen grandparent.
The frozen source remains reachable in trusted `main` history via the
second-parent chain of merged #1951, even though it is not on the current
`main` *first-parent* path. This is intentional, permitted only because
the entire trio is separately source-pinned and validated.

## Independent trusted dispatch and origin authority

The **controller and credentials still come from current trusted main**:
manual owner/first-attempt dispatch, exact `github.sha`, clean checkout,
and a live read of `main` equaling that dispatch SHA. The current main
may advance later, but must not advance *during* a trial that requires
`main` stability. An old pinned target may never replace the trusted
controller checkout or become a credential-bearing execution source.

All four W3 jobs fetch full trusted Git history. Before an original W3 run,
`snapshot_tree()` verifies the first-parent edges, the frozen source's
reachability from current main, and all three target workflow subtree SHAs.
No target workflow is executed by the controller. None of the three
selected target commits is recomputed from `HEAD^1` or `HEAD^1^1`.

A revised **`MHB-ATC-W3-ORIGIN-V2`** binding records, separately:
- the authenticated owner/main workflow **dispatch_sha**;
- the exact source-pinned frozen source/parent/grandparent;
- the original run ID, first-attempt/mode/actor/repository/nonce and
  independently reviewed workflow-tree pin.

For independent recovery, the GitHub Actions original-run GET must match
`dispatch_sha` (not frozen `source_sha`). The downloaded durable original
binding must match the current reviewed frozen target policy exactly, and
authenticated GitHub Git object GETs independently verify both target
first-parent edges and all three workflow subtree SHAs. Cleanup acts on
only the original exact disposable ref names with known frozen target SHAs;
it does not infer new test targets from a later `main`. Ambiguous results
retain INTENT/STOP/UNKNOWN_AFTER_REQUEST and STOP_INCOMPLETE; no retry.

The **`MHB-ATC-W3-PARTIAL-EVIDENCE-V2`** ledger carries both the
trusted `dispatch_sha` and frozen `source_sha` so no receipt can
silently equate those two trust roles.

## Separate current-default workflow quarantine for DELETE

**Two distinct workflow sources require two distinct checks.** The frozen
S/P/G Git tree pin covers CREATE, UPDATE and FORCE-UPDATE targets. GitHub
uses the **current repository default-branch SHA and its workflows** for
a branch `delete` event, and branch-deletion push events can report that
default-branch SHA. Freezing S/P/G therefore does **not** quarantine DELETE.

Before the publisher's canary DELETE, the worker's negative DELETE (which
could unexpectedly succeed), and **each** publisher cleanup DELETE, the
trusted controller performs a fresh, authenticated read of the repository
identity and `default_branch: main`, reads the live `main` SHA, and checks
the **entire workflow inventory at that exact current-default commit**.
It runs the same strict G1 YAML event parser and W3 branch-disjointness
predicates used by the hosted full-inventory tests, rejecting unsupported
events, any `on: delete` event, any push selector that can reach the W3
disposable namespace, and malformed/unknown selectors. Current main may
have *different* workflows from frozen S/P/G if the complete current-default
inventory passes semantic quarantine.

The new `scripts/mhb_atc_w3_default_quarantine.py` reads Git blobs as
**data only** (no checkout, workflow execution, hooks or submodules). It
binds the semantic inventory result to the authenticated exact default
commit SHA and its Git `.github/workflows` tree. When main advances
beyond the checkout's Git objects, it may fetch public Git data read-only,
then requires the fetched head to match the authenticated SHA. An unsafe,
missing, ambiguous or changed default context stops without DELETE.

The controller reads default main again after validation and immediately
before the request. Source-defined `W3_DEFAULT_QUARANTINE` evidence and
the fsynced JSON `default_quarantine_checks` array retain the **operation,
current-default SHA and current-default workflow-tree SHA**, independently
of the frozen test tree pin. A changed default is **never** accepted merely
because the previous job or prior recovery plan validated an earlier SHA:
recovery explicitly revalidates its own current default before any cleanup.

The checks do not make GitHub's ordinary branch DELETE atomic with a
concurrent `main` update. A main move *after* the last pre-request GET
but before GitHub processes DELETE is an inherent residual race; without
a server-side transaction or an independently enforced freeze of default
changes, no proof of perfect concurrency exclusion is claimed. Treat any
ambiguous mutation or unexpected fanout as STOP with independent ref
reconciliation. This is not a substitute for the separate actual publisher
push-fanout commissioning gate or its disabled source flag.


## Explicit STOP conditions / separate live dependencies

- An unsafe/missing current-default semantic workflow inventory, a changed
  default-branch identity, or default SHA drift between validation and DELETE.
- Any malformed, foreign, noncanonical or mismatched source policy tuple;
  a frozen source not reachable from trusted main; wrong Git first-parent
  edge; mismatched workflow tree; incorrect original Actions run metadata;
  untrusted/missing receipt or unknown cleanup SHA.
- Any previously privileged cancellation/unbounded retry, unexpected
  repository event, drifted `main` before a protected attempt, changed
  ruleset or App identity, ambiguous/allowed worker operation, and any
  direct worker PR CREATE/REOPEN path.
- Live authorization remains **false**. `approved_nonce` is **null** and
  `push_ci_quarantine_verified` is **false**. No reviewer acceptance of
  this PR implies acceptance of a live publisher-origin push-fanout test.
- Later: independently authorized safe publisher App push-fanout observation,
  fresh never-reused nonce and explicit activation PR, protected runtime
  variables/environments, real W3 negative operations, full ref-state
  reconciliation and independently proven App-token revocation.

## Review questions and proof obligations

1. Is the frozen trio a valid, immutable, reachable first-parent chain
   within trusted merged main history, even though it appears on an
   earlier PR branch's first-parent history? Are the three Git workflow
   subtrees exactly the reviewed safe `4b8b338a…` object?
2. Does each credential-bearing original job run only current
   trusted-main controller source, with Git history available to verify
   the frozen trio before any token-bearing ref operation?
3. Does V2's authenticated original **dispatch_sha** remain distinct from
   the frozen ref source throughout recovery, evidentiary receipts and
   real `main` drift checks?
4. Do changed/missing/malicious origin bindings, first-parent links,
   tree hashes or token-protocol results fail closed, preserving exact
   authorized cleanup and no false denial/cleanup completion?
5. Are current-default workflow semantics independently checked at the exact
   live default SHA/tree before the publisher canary DELETE, worker DELETE,
   and each cleanup/recovery DELETE? Can safe new main workflows pass while
   unsafe branch-trigger or delete events fail before the API write?
6. Does every default check produce a separate SHA/tree-bound durable receipt
   and revalidate after default changes, without confusing current-default
   evidence with frozen historical target identity?
7. Are strict four-request scope, independently reviewed publisher cleanup,
   worker App isolation and all disabled activation gates unchanged?

Run offline W3 provenance/ref-trial/evidence and G1 full-inventory suites,
then hosted Radar Replay and required PR CI on the final exact head.
Independent acceptance must bind the actual new head and all target
commit SHA/tree values; no live commissioning is part of this review.
