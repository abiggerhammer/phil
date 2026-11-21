# W3 publisher-App fanout: one-use nonce reservation ledger

This is a human-reviewed reservation ledger, NOT a credential source, GitHub
branch-lock, automatic nonce-consumption proof, or permission to dispatch a
live publisher App operation.

| Candidate nonce | Entered (CET) | Purpose | State | Approval / execution |
| --- | --- | --- | --- | --- |
| d948536ad68f | 2026-11-20 | One supervised W3 publisher-App fanout canary | **SPENT — DO NOT REUSE** | Owner-authorized original [run #44877317938](https://github.com/abiggerhammer/phil/actions/runs/44877317938); CREATE HTTP 201 at pinned target, DELETE HTTP 204, verified empty admitted namespace and both App-token post-job revocations. Event-census comparison: zero new runs; independent quarantine/fanout review still required |

The candidate was generated using a cryptographic random 6-byte value.
At drafting time, searching the connected Phil repository code and GitHub
issues returned no occurrence. That search cannot prove non-use in external
ledgers, historic deleted runs, or records inaccessible to this connection.
The repository owner must explicitly reconcile those records and confirm the
nonce's eligibility before using it.

Reservation discipline:

1. One nonce can belong to only one proposed original owner/manual fanout run.
2. Never recycle the candidate once attempted, even if CREATE failed, the
   branch was deleted, or cleanup eventually succeeded.
3. Before any live run, the repository owner explicitly confirms the nonce
   and separately approves the exact reviewed activation source SHA.
4. Only the independently reviewed original-run binding and live GitHub
   evidence can establish which real Actions run used the nonce; this
   Markdown file is not that evidence.
5. If abandoned or superseded, mark the nonce RETIRED-UNUSED, never recycle
   it as fresh. For an executed attempt, mark SPENT with the exact run ID
   and the independently reconciled cleanup/absence receipts.
6. Human updates to this ledger require a separate reviewed PR; no
   unattended worker or observer may change activation policy from it.

See the source-only activation packet at
docs/phase-2/mhb-atc-w3-fanout-activation-packet-20261120.md.

## Execution evidence for spent nonce `d948536ad68f` (2026-11-21)

The owner explicitly approved one supervised execution after Astra's technical
ACCEPT of source activation PR #1969. Original owner/manual first-attempt
[Actions run #44877317938](https://github.com/abiggerhammer/phil/actions/runs/44877317938)
used dispatch SHA `338a12849611e72610fb6ee1194dc9495935588f`.
Authenticated origin artifact `14696605839` was uploaded before token mint.

- [CREATE job](https://github.com/abiggerhammer/phil/actions/runs/44877317938/job/136765012469): exact
  `refs/heads/hamster/admitted/w3-fanout-d948536ad68f-canary` at
  `e38814a2e916252a8a7f3dd438943e8f4a21664a`; HTTP 201, exact ref
  readback and VERIFIED receipt; evidence artifact `14696805980`;
  action post-job log states `Token revoked`.
- [CLEANUP job](https://github.com/abiggerhammer/phil/actions/runs/44877317938/job/136766092059):
  authenticated original-run recovery, HTTP 204, exact ref absent, empty
  protected namespace, VERIFIED receipt; evidence artifact `14696687076`;
  its separate action post-job log states `Token revoked`.
- The live default-workflow quarantine reported commit
  `338a12849611e72610fb6ee1194dc9495935588f` and workflow tree
  `f73817adc849d925b258ea40775b981787ceb100` for both mutations.
- The owner-supplied observer comparison reported `before_count=1`,
  `after_count=1`, `new_total=0`, no potential candidate run IDs, and
  `observation_lag_seconds=2001`. The decision was
  `NO_CANDIDATE_RUNS_REVIEW_REQUIRED`, **not** quarantine certification.
  Independent inspection of the raw before/after census artifacts, identical
  UTC bounds, delayed/incomplete delivery and attribution remains outstanding.

All three workflow artifacts are retained only until approximately
2026-12-21; preserve them before expiration. **SPENT** means this nonce is
never eligible for another original `mode=run` dispatch. Authenticated
`mode=cleanup` recovery of the original run remains permitted if needed,
independent of cleanup success or any eventual verdict on event fanout. The separate W3 worker/admission
source remains disabled; no automatic promotion of
`push_ci_quarantine_verified` is justified. See the audit evidence in
[#1839](https://github.com/abiggerhammer/phil/issues/1839#issuecomment-7058933619).
