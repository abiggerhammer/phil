# INT-006 external smoke evidence — 2026-09-12

This record retains the outside-user release evidence required by
`PHIL-P1-STEVE-RELEASE-001` and the Phase-1 `INT-006` exit case.

Both testers used the published GitHub Release `steve-v0.1.1-phase1`, downloaded
through an ordinary web browser, and ran the Apple-Silicon macOS package without
removing quarantine or using a Gatekeeper bypass.

## Liz

- Tester: Liz (“Lizzard” in the retained Signal conversation)
- Date: 2026-09-12
- Time reported to Meredith: 19:17 Europe/Brussels
- Browser: Firefox
- Release: `steve-v0.1.1-phase1`
- Platform reported by the package smoke: `Darwin 24.6.0 arm64`
- Result: `PASS: packaged Phase-1 Steve put/get and corruption smoke`
- `release_package_sha256`: `f4505c331079d37c1bf07f0e10729db0f8376390404bd93e2c0f1f019f2dca10`
- `package_manifest_sha256`: `b43cc254d99417dae7baeeacbec80f3222e3ba2732e33b26a10de311f25df296`
- Browser-download / Gatekeeper issues: none reported after the corrected signed/notarized 0.1.1 release; no bypass was used.

## Pete

- Tester: Pete Wolfendale
- Date: 2026-09-12
- Release: `steve-v0.1.1-phase1`
- Browser: ordinary browser download (reported as Safari by Meredith, with browser choice not material to the exit claim)
- Platform reported by the package smoke: `Darwin 22.6.0 arm64`
- Result: `PASS: packaged Phase-1 Steve put/get and corruption smoke`
- `release_package_sha256`: `f4505c331079d37c1bf07f0e10729db0f8376390404bd93e2c0f1f019f2dca10`
- `package_manifest_sha256`: `b43cc254d99417dae7baeeacbec80f3222e3ba2732e33b26a10de311f25df296`
- Browser-download / Gatekeeper issues: none reported; no quarantine removal or Gatekeeper bypass was used.

## Interpretation

The two independent outside-user runs exercised the same published 0.1.1 package
identity and both reached the required final PASS result on supported Apple-Silicon
Darwin systems. Together with the repository's permanent signed/notarized release
pipeline and package/TCB disclosure, this satisfies the external-use evidence
boundary for `PHIL-P1-STEVE-RELEASE-001` / `INT-006`.

The original Signal screenshots are retained privately by Meredith and are not
committed to the public repository; this document records only the evidence fields
required by the public smoke protocol.
