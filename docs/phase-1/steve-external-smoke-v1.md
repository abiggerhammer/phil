# Steve Phase-1 external smoke v1

This protocol supplies the human external-use evidence for
`PHIL-P1-STEVE-RELEASE-001`.

The tester must start from the published GitHub Release
`steve-v0.1.0-phase1`, using an ordinary web browser to download the archive for
their supported platform and its adjacent `.sha256` file. They do not need the
GitHub CLI, a Phil checkout, Cabal, GHC, LLVM, or implementation knowledge.

## Supported environments

Phase 1 supports these Steve release targets:

- x86-64 Linux with ordinary POSIX filesystem semantics;
- Apple Silicon macOS (`aarch64-apple-darwin`) with ordinary POSIX filesystem
  semantics.

The package smoke requires a shell with `tar`, `grep`, and `cmp`, plus one of:

- Linux: `sha256sum`;
- macOS: `shasum` (used as `shasum -a 256`).

## Download

Open the Phil repository's GitHub Releases page in a browser and select
`steve-v0.1.0-phase1`.

For Apple Silicon macOS, download:

- `phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz`
- `phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz.sha256`

For x86-64 Linux, download:

- `phil-steve-0.1.0-phase1-x86_64-linux.tar.gz`
- `phil-steve-0.1.0-phase1-x86_64-linux.tar.gz.sha256`

Do not use an Actions artifact or a repository checkout for the closeout smoke;
the public GitHub Release is the distribution boundary being tested.

## Apple Silicon macOS procedure

Put the two downloaded files in an otherwise unrelated directory, then run:

```sh
shasum -a 256 -c phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz.sha256
tar -xzf phil-steve-0.1.0-phase1-aarch64-apple-darwin.tar.gz
cd phil-steve-0.1.0-phase1-aarch64-apple-darwin
./smoke-test.sh
```

If macOS presents a Gatekeeper/quarantine prompt or otherwise blocks execution,
record that as a usability/setup failure before applying any workaround. The
point of the initial external smoke is to expose exactly that kind of release
friction rather than silently routing around it.

## x86-64 Linux procedure

Put the two downloaded files in an otherwise unrelated directory, then run:

```sh
sha256sum -c phil-steve-0.1.0-phase1-x86_64-linux.tar.gz.sha256
tar -xzf phil-steve-0.1.0-phase1-x86_64-linux.tar.gz
cd phil-steve-0.1.0-phase1-x86_64-linux
./smoke-test.sh
```

The smoke script verifies the package's own `SHA256SUMS`, checks exact TCB-copy
agreement, starts the shipped ordinary `philc`, performs a real PUT and GET
through packaged Steve, and verifies that deliberately corrupted CAS content
cannot replace an existing output file.

Success ends with output of this shape:

```text
PASS: packaged Phase-1 Steve put/get and corruption smoke
platform=...
release_package_sha256=...
package_manifest_sha256=...
```

## Evidence to retain

Record:

- tester identity or stable attribution sufficient to establish that the tester
  was outside the implementation team;
- date;
- the GitHub Release tag `steve-v0.1.0-phase1`;
- operating-system and machine information from the `platform=` line;
- archive SHA-256 from the downloaded `.sha256` file;
- the complete final PASS/evidence lines from `smoke-test.sh`;
- any unexpected browser-download, unpacking, Gatekeeper, setup, or usability
  problem encountered before the smoke passed.

A successful run is evidence of human package usability. It does not expand the
certified platform or trust boundary beyond the selected release package's own
records.
