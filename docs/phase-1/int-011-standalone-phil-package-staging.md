# INT-011 standalone Phil package staging

This slice establishes the package-construction and package-only consumer-smoke boundary for the standalone Phil Phase-1 distribution.

Authoritative staging evidence: GitHub Actions run `34668066140` on exact staged head `7c04ee35ae11da805646c7817d1b1e6c7884fdde`.

Both native platform jobs passed:

- x86-64 Linux: built `phil-0.1.0-phase1-x86_64-linux.tar.gz`, verified its adjacent checksum, unpacked it into a fresh consumer directory, and passed `./smoke-test.sh` with exact target `x86_64-unknown-linux-gnu`.
- Apple Silicon Darwin: built unsigned staging `phil-0.1.0-phase1-aarch64-apple-darwin.zip`, verified its adjacent checksum, unpacked it into a fresh consumer directory, verified a native arm64 Mach-O with `LC_BUILD_VERSION` minimum macOS 11.0, and passed `./smoke-test.sh` with exact target `aarch64-apple-darwin`.

The package smoke requires explicit target selection, rejects unknown targets, lowers accepted representative source with exact target triple/data layout, checks scalar binding preservation, and rejects representative invalid source.

The Darwin artifact in this slice is deliberately staging-only. Developer ID signing, Apple notarization, certified release/TCB binding, permanent release CI, GitHub Release publication, and outside-user browser-download smoke with quarantine intact remain later INT-011 work.
