# MHB-ATC commissioning smoke test — 2026-11-06

This file exists solely to exercise the opt-in MHB air traffic control path:

1. Stage this branch at its exact commit SHA with a trusted repository_dispatch event.
2. Verify that a durable, labelled staged-candidate issue is created without opening a PR.
3. Run the admission controller in read-only dry-run mode.
4. Explicitly admit one PR; verify that PR-triggered CI begins and receives exact-head checks.
5. Close the test PR and candidate issue without merging this test-only file.

This is documentation-only test data. It does not modify Phil code, proof
artifacts, runtime behavior, or CI authorization policy.

**The test PR must not be merged.** Its purpose is to verify integration,
not to alter the released tree.
