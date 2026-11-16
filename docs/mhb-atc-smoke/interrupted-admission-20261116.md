# MHB-ATC interrupted-reservation recovery commissioning fixture

**2026-11-16. Disposable / never merge.**

This benign file exists only to create a distinct staging branch for exercising the existing recovery planner. It modifies no source, semantics, workflow or assurance code. The branch must not be opened as a PR and the test candidate must not be merged.

Planned controlled fault-injection sequence:
1. Stage this exact SHA through the trusted `mhb-atc-stage` repository-dispatch workflow, obtaining a bot-created `atc: staged` issue.
2. With no PR from this branch, inject a simulated interrupted admission by changing **only** that issue's candidate state from `atc: staged` to `atc: admitting`. No `admit-one` run or PR creation is authorized by this fixture.
3. Invoke reconciliation in `dry-run` before the reservation age reaches 15 minutes. Expect `hold` and no writes.
4. At or after 15 minutes from the real issue `updated_at`, allow automatic reconciliation or trigger the existing `reconcile` workflow; expect `retry`, exact SHA preserved, no matching PR, and a return to `atc: staged`.
5. Record positive recovery evidence; then close this disposable candidate without merging anything.

Do not edit or comment on the candidate after fault injection: the code uses issue `updated_at` as the reservation-age clock, and additional writes can reset the 15-minute grace. Record notes on the parent commissioning issue instead.
