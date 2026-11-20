# W3 publisher-App fanout: one-use nonce reservation ledger

This is a human-reviewed reservation ledger, NOT a credential source, GitHub
branch-lock, automatic nonce-consumption proof, or permission to dispatch a
live publisher App operation.

| Candidate nonce | Entered (CET) | Purpose | State | Approval / execution |
| --- | --- | --- | --- | --- |
| d948536ad68f | 2026-11-20 | One supervised W3 publisher-App fanout canary | PROPOSED-RESERVED, NOT APPROVED | No owner authorization, no source/runtime activation, no live run |

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
