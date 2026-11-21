# W3 deletion selector: inert positive-control implementation packet

**SOURCE ONLY — NOT AUTHORIZED TO RUN.** These are fixtures inside Phil's
`experiments/` tree, NOT active Phil Actions workflows. Source plan #1980,
assurance case #1979, audit issue #1839.

## Eight exact workflow inputs

Four YAML files under each of `fixtures/target_v1/.github/workflows` and
`fixtures/default_v1/.github/workflows` have identical trigger selectors:
UNFILTERED handles `push`/`create`/`delete`; MAIN_ONLY accepts only
`push.branches:[main]`; W3_ONLY accepts only
`push.branches:['hamster/admitted/w3-*']`; IGNORE_PAIR has exactly
`['hamster/staged/**','hamster/admitted/w3-*']`.

Their only intended behavior difference is the fixed TARGET_V1 versus
DEFAULT_V1 source marker. Both source revisions must be fully archived
before any disposable repository is deleted. Witness steps use
`permissions: {}`, a two-minute hosted runner, no checkout, no third-party
actions, no secrets, and no repository writes. The witness emits a single
`W3_WITNESS_JSON:` record; event flags are parsed as literal JSON
booleans/null, never shell truthiness.

## Separate owner-approved disposable test repository — NOT Phil

Before execution Astra must review the full exact code and fixture bytes,
the command/evidence packet, and the intended credential. The owner must
select and approve a test-only repo named
`OWNER/w3-delete-selector-probe-NAME`, a fresh one-use 12-hex nonce,
target commit T, default workflow commit D, and a test-only local
credential; no Phil App/private key may be used. The client explicitly
rejects the production Phil repo, refuses to run in Actions, and only
writes exact W3 disposable branch refs in the approved test repo. Its
repo-name guard is not itself authorization.

1. In a local *test repository clone*, install the four TARGET_V1 YAML
   files into its root `.github/workflows/`, commit them as T.
2. Replace them with the four DEFAULT_V1 files, commit as D and push to
   the test repository's `main`. Record both SHAs and workflow bytes.
3. Wait for setup CI to settle. During Phase A, perform one ordinary
   empty main commit and push from the owner-local clone to exercise
   UNFILTERED/MAIN_ONLY/IGNORE_PAIR positive controls. Record the new
   main SHA M (same DEFAULT_V1 workflow bytes).
4. On the exact reviewed Phil implementation head, run read-only
   `probe.py plan` using the test repo, T, M, and the fresh nonce.
   It checks test repo identity, current main, exact source bytes at T
   and M, target existence and the entire admitted-prefix occupancy.
5. In **distinct UTC windows**, take a before snapshot, do at most one
   separately authorized Phase B REST CREATE, wait through the full
   window plus 30 minutes, take the matching after snapshot, and
   classify. Only if CREATE controls succeed, separately authorize
   a new window and the one-time experimental Phase C DELETE.
6. If CREATE succeeds but Phase B becomes INCONCLUSIVE/STOP, use a
   separately authorized `abort-cleanup` (after exact GET reconciliation)
   in its own window. This remains abort-cleanup evidence, NEVER
   a successful experimental Phase C result. If a prior response or
   target is ambiguous, STOP rather than retry.

The initial operator command syntax **for review only** is:

    PROBE=experiments/w3-deletion-selector/probe.py
    TEST_REPO='OWNER/w3-delete-selector-probe-APPROVED'
    REPO_ID='PINNED_NUMERIC_TEST_REPO_ID'
    NONCE='REPLACE_WITH_FRESH_12_HEX'
    TARGET_SHA='40-hex-target-T'
    DEFAULT_SHA='40-hex-main-M'
    STATE_DIR='/owner-private-w3-evidence'

    python3 "$PROBE" plan --repo "$TEST_REPO" --repo-id "$REPO_ID" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA"

    # BEFORE a separately authorized CREATE in its own fixed UTC window
    python3 "$PROBE" snapshot --repo "$TEST_REPO" --repo-id "$REPO_ID" --nonce "$NONCE" \
      --window-start 'YYYY-MM-DDTHH:MM:SSZ' \
      --window-end 'YYYY-MM-DDTHH:MM:SSZ' \
      --out "$STATE_DIR/phase-b-before.json"

    # Separately authorized mutation ONLY in disposable repo:
    python3 "$PROBE" create --repo "$TEST_REPO" --repo-id "$REPO_ID" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --state-dir "$STATE_DIR" --confirm CREATE_TEST_ONLY

    # AFTER same window + at least 30m lag, collect same bounds to new path
    python3 "$PROBE" classify --phase create \
      --before "$STATE_DIR/phase-b-before.json" \
      --after "$STATE_DIR/phase-b-after.json"

    # Separate later approved Phase C:
    python3 "$PROBE" delete --repo "$TEST_REPO" --repo-id "$REPO_ID" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --state-dir "$STATE_DIR" --confirm DELETE_TEST_ONLY

    # Separate abort path if Phase B is inconclusive after CREATE:
    python3 "$PROBE" abort-cleanup --repo "$TEST_REPO" --repo-id "$REPO_ID" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --state-dir "$STATE_DIR" --confirm ABORT_CLEANUP_TEST_ONLY

`mkdir -m 700 "$STATE_DIR"` must be done before any write, in a
private owner-local directory. Nonce-phase intent markers are opened
exclusively and fsynced **before** REST requests; cleanup and normal
DELETE share the same one-use marker. No automatic retries.

## Critical classification boundaries

A genuine Phase C positive result requires **both UNFILTERED and W3_ONLY**
to report `event_name=push`, `event_deleted=true` (actual Boolean),
`event_created=false`, and the exact same deleted payload ref.
MAIN_ONLY or IGNORE_PAIR observing that deletion-caused push is a
COUNTEREXAMPLE/STOP. An absent deletion witness, delayed Phase B
creation run, invalid Boolean, incomplete paging or unavailable
run logs is INCONCLUSIVE. An independent main-push control must prove
the main-only and ignore-pattern witnesses are active.

A supporting result is `SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED`, never a
general GitHub event-delivery theorem. No change to Phil
`push_ci_quarantine_verified`, `live_authorized`, runtime switches,
nonce, App permissions or W3 ref namespace follows automatically.
The post-last-GET race and the fanout recovery verifier's
current-false quarantine precondition remain separate obligations.

## Review and evidence retention

Run `python3 experiments/w3-deletion-selector/test_probe.py` offline.
The implementation reviewer must examine actual YAML version selection,
one-use mutation gate, test-repository identity, owner credential
scoping, exact ref/SHA checks, event payload flags, capture windows,
pagination, delayed-tail handling, and abort cleanup. Export all eight
**actual fixture bytes**, test repository workflow Git objects and
selected source versions, GitHub API response statuses, raw run logs,
the curated before/after inventories, the phase-specific classifier
outputs and SHA-256 hashes before considering test repository deletion.
A bounded run inventory is NOT a delivery-completeness proof.
