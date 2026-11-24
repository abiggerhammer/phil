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
3. Wait for setup CI to settle. Take the Phase A before snapshot
   while `main` is at D. The separately approved control would advance
   `main` with one empty commit M whose sole parent is D. After the
   observation delay, take the Phase A after snapshot at M and classify
   the pair. The UNFILTERED, MAIN_ONLY and IGNORE_PAIR controls must
   bind to M.
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
    APPROVED_ACTOR='OWNER_APPROVED_GITHUB_LOGIN'
    NONCE='REPLACE_WITH_FRESH_12_HEX'
    TARGET_SHA='40-hex-target-T'
    SETUP_SHA='40-hex-main-D'
    DEFAULT_SHA='40-hex-main-M'
    STATE_DIR='/owner-private-w3-evidence'
    PHASE_A_START='YYYY-MM-DDTHH:MM:SSZ'
    PHASE_A_END='YYYY-MM-DDTHH:MM:SSZ'

    # Phase A before capture at D, within the Phase A window:
    python3 "$PROBE" snapshot --repo "$TEST_REPO" --repo-id "$REPO_ID" \
      --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$SETUP_SHA" \
      --window-start "$PHASE_A_START" --window-end "$PHASE_A_END" \
      --out "$STATE_DIR/phase-a-before.json"

    # Phase A after capture at M, at least 30m after the same window ends:
    python3 "$PROBE" snapshot --repo "$TEST_REPO" --repo-id "$REPO_ID" \
      --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --main-before-sha "$SETUP_SHA" \
      --window-start "$PHASE_A_START" --window-end "$PHASE_A_END" \
      --out "$STATE_DIR/phase-a-after.json"
    python3 "$PROBE" classify --phase main \
      --before "$STATE_DIR/phase-a-before.json" --after "$STATE_DIR/phase-a-after.json"

    python3 "$PROBE" plan --repo "$TEST_REPO" --repo-id "$REPO_ID" --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA"

    # BEFORE separately authorized CREATE in one fixed UTC window:
    python3 "$PROBE" snapshot --repo "$TEST_REPO" --repo-id "$REPO_ID" \
      --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --window-start 'YYYY-MM-DDTHH:MM:SSZ' \
      --window-end 'YYYY-MM-DDTHH:MM:SSZ' \
      --out "$STATE_DIR/phase-b-before.json"

    # Separately authorized mutation ONLY in disposable repo:
    python3 "$PROBE" create --repo "$TEST_REPO" --repo-id "$REPO_ID" \
      --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --state-dir "$STATE_DIR" --confirm CREATE_TEST_ONLY

    # AFTER same fixed window + at least 30m lag, take SECOND snapshot:
    python3 "$PROBE" snapshot --repo "$TEST_REPO" --repo-id "$REPO_ID" \
      --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --window-start 'YYYY-MM-DDTHH:MM:SSZ' \
      --window-end 'YYYY-MM-DDTHH:MM:SSZ' \
      --out "$STATE_DIR/phase-b-after.json"
    python3 "$PROBE" classify --phase create \
      --before "$STATE_DIR/phase-b-before.json" \
      --after "$STATE_DIR/phase-b-after.json" \
      --intent "$STATE_DIR/$NONCE.create-intent.json"

    # Separate later approved Phase C:
    python3 "$PROBE" delete --repo "$TEST_REPO" --repo-id "$REPO_ID" --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
      --target-sha "$TARGET_SHA" --default-sha "$DEFAULT_SHA" \
      --state-dir "$STATE_DIR" --confirm DELETE_TEST_ONLY

    # Separate abort path if Phase B is inconclusive after CREATE:
    python3 "$PROBE" abort-cleanup --repo "$TEST_REPO" --repo-id "$REPO_ID" --actor "$APPROVED_ACTOR" --nonce "$NONCE" \
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
COUNTEREXAMPLE/STOP. An absent required deletion witness is INCONCLUSIVE; delayed Phase B
creation traffic, invalid Boolean, incomplete pagination or unavailable
run logs are a STOP or fail-closed ambiguity, never positive evidence. An independent main-push control must prove
the main-only and ignore-pattern witnesses are active.

A supporting result is `SUPPORTS_MODEL_BOUNDED_NOT_CERTIFIED`, never a
general GitHub event-delivery theorem. No change to Phil
`push_ci_quarantine_verified`, `live_authorized`, runtime switches,
nonce, App permissions or W3 ref namespace follows automatically.
The post-last-GET race and the fanout recovery verifier's
current-false quarantine precondition remain separate obligations.

## Review and evidence retention

Run `python3 -B experiments/w3-deletion-selector/test_probe.py -v` offline.
The implementation reviewer must examine actual YAML version selection,
one-use mutation gate, test-repository identity, owner credential
scoping, exact ref/SHA checks, event payload flags, capture windows,
pagination, delayed-tail handling, and abort cleanup. Export all eight
**actual fixture bytes**, test repository workflow Git objects and
selected source versions, GitHub API response statuses, raw run logs,
the curated before/after inventories, the phase-specific classifier
outputs and SHA-256 hashes before considering test repository deletion.
A bounded run inventory is NOT a delivery-completeness proof.


## Source-only security repair contract (2026-11-22; PR #1982)

**Nothing in this directory is approved for live testing or commissioning.**
PR-only offline tests and CI cannot prove GitHub event-delivery semantics,
effective token limitations, run-log authenticity, or signed environment
provenance. An independent Astra review of the exact repaired HEAD is
mandatory before any merge, and *separate human security authorization*
would be required before a live disposable experiment.

The GitHub.com client deliberately fixes REST to
`https://api.github.com`, obtains a token only for `github.com` via
`gh auth token --hostname github.com`, and checks the authenticated
`GET /user` principal against the separately approved `--actor`.
`GH_HOST` targeting anything other than GitHub.com and enterprise-token
context fail closed. The log command is explicitly passed the **same**
token, `GH_HOST=github.com`, immutable repo slug and run ID with
`--attempt 1`, never an implicitly different CLI credential/host.
The client checks repository-owner/name/numeric ID, original run API
and HTML URLs, run repository ID, original attempt, actor, head SHA,
workflow path/ref, witness SHA/actor/run ID and exact selected source
marker. The repo name pattern alone is **not** authorization.

For each source revision, the eight fixture bytes must match the
independently selected exact target/default commits. Snapshot now
requires `--target-sha`, `--default-sha` and `--actor` in addition to
repo and numeric ID. It preserves one `W3-SELECTOR-CENSUS-V3` file per
before/after observation, event-by-event pinned pagination counts, and
each retrieved log's SHA-256 and retrieval-status evidence. Changing
totals, short/missing pages, duplicate IDs, outside-window runs,
unexpected repository/actor/run URL, replay attempt or source SHA
**STOP**, not a truncated apparent success. A stable REST count still
is not a cryptographic consistency snapshot and cannot prove that no
unreported GitHub event exists. Both Phase A captures verify the
DEFAULT_V1 bytes at their pinned main revisions. The after capture
additionally checks that M has D as its sole parent and the same Git
tree. Phases B and C require an unchanged default SHA within each pair.

`classify --phase create|delete` now **requires `--intent`** pointing
to the exact successful one-use mutation receipt. The approved action
must match the phase, and its prepared/request/completion times must
fall between the clean pre-mutation snapshot and the bounded
post-mutation snapshot. Runs earlier than the recorded request start
are unexpected. Timestamps have whole-second resolution and equality
is allowed, so this check establishes ordering at the recorded resolution. A typed successful `abort-cleanup` has a
*separate* `ABORT_CLEANUP_STATE_VERIFIED` decision; it can never
satisfy Phase C, even if a deletion-looking push witness exists.
`ALREADY_ABSENT_NO_WRITE` cannot satisfy either planned phase.

The before inventory must contain no observed runs in the selected
event window. All after-window `push`, `create`, and `delete`
runs are accounted for; only the correct, independently bound
UNFILTERED auxiliary branch events are allowed as context. CREATE
uses the created W3 ref and target SHA. DELETE uses the default ref
and SHA. Both must name the experimental branch and carry
`event_ref_type=branch`. Auxiliary events supply no positive push
witnesses. Any other event run,
invalid log, duplicate control, wrong ref/timestamp/SHA/actor or
missing response is `STOP_UNRELATED_OR_AMBIGUOUS_TRAFFIC`. A valid
forbidden filter witness is a `COUNTEREXAMPLE_STOP`. The absent
required positive remains `INCONCLUSIVE_MISSING_POSITIVE_WITNESS`,
not a failure observation or certification.

Both UNFILTERED and W3_ONLY planned Phase C controls must carry
**literal JSON** `event_deleted=true` and `event_created=false`,
with the exact selected deleted ref. The fixed TARGET_V1/DEFAULT_V1
markers must agree with each run's independently selected target or
default SHA and workflow ref. The eight inert YAML fixtures remain the only designed positive
controls. Their V2 witness records include the typed payload ref kind.
The log parser reads records at the start of runner messages after
removing the CLI log prefix and runner timestamp. Duplicate or malformed
emitted records remain ambiguous. A signed provenance claim,
full native GitHub ref/response isolation, concurrent event absence,
and effective GitHub App/ruleset permissions remain explicitly open.

Fail-closed directory durability: the exclusive one-use intent file
and its containing directory must both be `fsync`ed **before**
any prospective mutation call. Errors abort without retries, leaving
the one-use path occupied. Poststate reconciliation is separate and
cannot retroactively make an unfynced intent safe. Do not run the
source mutator to exercise this guarantee outside mocked offline tests.

## Private HTTP diagnostic receipts

On an attempted mutation with an unexpected HTTP response, the probe
preserves a mode-0600 sidecar beside the consumed intent in the
owner-private state directory. A transport or response-processing
failure also receives an unavailable diagnostic when preservation
succeeds. The sidecar binds the operation, repository, actor, nonce,
exact ref and source SHAs, UTC timestamps, and probe file SHA-256.
Its diagnostic digest covers the canonical JSON of the sanitized
diagnostic object. It does not cover the original response bytes.

- `complete` requires both confirmed HTTP framing and a bounded JSON
  error object. Declared lengths must be satisfied. Chunked bodies
  require a terminating chunk and final trailer delimiter. For a
  close-delimited response the HTTP reader must observe EOF. Such EOF
  satisfies HTTP framing without proving the sender's intended length.
  Only a fixed message category and allowlisted, format-validated
  request ID or rate-limit fields are retained.
- `truncated` means the 4 KiB body cap was exceeded, as detected by
  reading one extra byte. No body text or partial message is retained.
- `unavailable` means there was no usable error body or HTTP response.
  Check the separately recorded HTTP status, which may be null.
- `failed` covers read errors, premature EOF, unconfirmed framing and
  invalid JSON or UTF-8. An ordinary mutation response that cannot be
  processed also records failed capture with its observed status and
  completion time, without retaining its body. A matching status and
  poststate cannot qualify that response as successful. If writing
  or syncing the sidecar fails, the intent records diagnostic failure
  when possible. The original durable marker remains consumed even if
  the intent summary itself cannot be updated. Sidecar presence alone
  does not establish successful preservation.

The sidecar never supplies success evidence. Preserve it privately with
the corresponding STOP receipt and disclose only independently reviewed
details. See the [GitHub support appendix](github-support-appendix.md)
for the historical diagnostic gap and unresolved platform questions.
