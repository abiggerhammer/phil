# CI: Hackage package-index retry pilot

On several November 2026 PRs, certificate matrix jobs failed in
`haskell-actions/setup@v2` with `curl: (92) HTTP/2 ... PROTOCOL_ERROR`
during the action's internal one-shot `cabal update`. Code and Rocq checks
passed, but affected certificate steps were skipped.

In `.github/workflows/phase0-back-certification.yml`, set
`cabal-update: false` on Haskell setup and run an explicit package-index
refresh using `scripts/ci/cabal-update-retry.sh`. The helper uses an
isolated temporary `CURL_HOME/.curlrc` requesting HTTP/1.1 for the
underlying curl executable; it attempts up to four `cabal update`
runs with 4-, 8-, and 16-second backoff. If all fail, it exits nonzero.
This does not bypass package-index refresh, mute errors, alter dependency
selection, or modify historical proof/certificate payloads.

A network-free test `scripts/ci/test-cabal-update-retry.sh`
verifies exact retry counts, backoff, scoped HTTP/1.1 configuration,
first-attempt success, and fail-closed exhaustion. One lightweight
`retry-helper-control` job gates the nine certificate matrix jobs.

This pilot deliberately affects only Phase 0 Back-Certification.
Other Haskell workflows still use their own setup routines; expansion
can follow after the bounded retry is independently checked.
PR-only supersession policy stays unchanged.
