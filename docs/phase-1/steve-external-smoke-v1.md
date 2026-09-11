# Steve Phase-1 external smoke v1

This protocol supplies the human external-use evidence for
`PHIL-P1-STEVE-RELEASE-001`.

The tester must start from a published `phil-steve-0.1.0-phase1-x86_64-linux`
archive and its adjacent `.sha256` file. They do not need a Phil checkout, Cabal,
GHC, LLVM, or implementation knowledge.

## Supported environment

- x86-64 Linux;
- ordinary POSIX filesystem semantics;
- a shell with `sha256sum`, `tar`, `grep`, and `cmp`.

The current Phase-1 package does not claim macOS or non-x86-64 support.

## Procedure

Put the archive and checksum file in an otherwise unrelated directory, then run:

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
- operating-system and machine information from the `platform=` line;
- archive SHA-256 from the downloaded `.sha256` file;
- the complete final PASS/evidence lines from `smoke-test.sh`;
- any unexpected setup or usability problem encountered before the smoke passed.

A successful run is evidence of human package usability. It does not expand the
certified platform or trust boundary beyond the release package's own records.
