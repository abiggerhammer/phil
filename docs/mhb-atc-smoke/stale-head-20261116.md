# MHB-ATC stale-head commissioning fixture

Test date: 2026-11-16.

**Never merge.** This disposable candidate deliberately tests an immutable SHA registry against a changed live branch ref.

Expected sequence:

1. Register this initial revision using the trusted `mhb-atc-stage` repository_dispatch event, creating a bot-authored candidate issue.
2. Once the issue exists, deliberately advance this same branch with a second harmless documentation commit, but do NOT repeat staging.
3. Invoke the existing manual ATC admit-one controller. It must reject the now-stale registered head **before** reserving a slot or creating a PR. A failed Actions job is the expected negative-test result.
4. Inspect issue labels, PRs, and logs; after preserving evidence, close the disposable stale candidate issue without merge to restore an empty queue.

No Phase 1 files, workflows, or target logic are changed; the branch is outside existing Phase 1 auto-PR patterns.
