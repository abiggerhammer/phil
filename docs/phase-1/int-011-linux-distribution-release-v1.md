# Phase 1 INT-011 Linux distribution release v1

## Purpose

INT-011 closes the gap between a repository checkout that can build Phil and a
standalone Phase-1 distribution that can be downloaded, verified, and used
without GHC, Cabal, LLVM, or a repository checkout.

This slice establishes the x86-64 Linux distribution identity. Apple Silicon
signing, notarization, quarantine-intact smoke, and final public release
publication remain subsequent INT-011 slices.

## Distribution assurance boundary

A standalone `philc` package is **not** modeled as a
`CertifiedReleaseArtifact`. That type certifies one exact checked Phil program
through its assurance manifest, StageClosure, target profile, emitted LLVM, and
residual application TCB.

The compiler distribution is a different object. INT-011 therefore introduces
a distribution identity that binds:

- package name and Phase-1 version;
- exact distribution target;
- exact source commit;
- SHA-256 of the frozen INT-007 top-level handoff manifest;
- SHA-256 of the packaged `philc` executable; and
- an explicit residual distribution TCB.

This does not claim the bootstrap compiler is independently verified. The
distribution record states the surviving trust boundary instead.

## Internal release record

Every certified Linux package contains:

`share/phil/phil.release-package`

with format header:

```text
PHIL-PHASE1-DISTRIBUTION-RELEASE-V1
```

The release ID is the SHA-256 identity of the canonical body containing the
package, source, handoff, compiler, and TCB records.

The required Phase-1 distribution trust-kind domain is exact:

- compiler/checker trust;
- native build-toolchain trust;
- LLVM language/toolchain trust; and
- target/host assumptions.

A missing kind, duplicate boundary identity, malformed digest, blank boundary,
or malformed source commit rejects before a release identity is constructed.

The Linux profile names the first Haskell compiler/checker implementation,
GHC/host linker/runtime, LLVM 18.x boundary, and x86-64 Linux host/ABI
assumptions explicitly.

## Frozen handoff root

The package includes an exact copy of:

`handoff/phase1/manifest-v1.tsv`

as:

`share/phil/phase1-handoff-manifest-v1.tsv`

The internal distribution record binds the SHA-256 of those exact bytes.
This gives a downloaded compiler package an explicit provenance edge back to the
complete INT-007 Phase-1 freeze without pretending that every frozen artifact
must be duplicated into the binary distribution.

## Package manifest and archive binding

`SHA256SUMS` content-addresses every file inside the unpacked package,
including the compiler, frozen handoff manifest, release record, TCB projection,
documentation, examples, and build metadata.

Because an archive cannot contain its own final digest without circularity,
INT-011 uses a second external record:

`phil-0.1.0-phase1-x86_64-linux.tar.gz.release`

with format header:

```text
PHIL-PHASE1-DISTRIBUTION-ARCHIVE-V1
```

The archive binding records:

- the exact internal distribution release ID;
- archive filename;
- archive SHA-256; and
- SHA-256 of the unpacked package's `SHA256SUMS`.

The archive-binding ID is itself canonical and deterministic. A separate
`.release.sha256` sidecar content-addresses that record.

## Human-readable TCB

`TCB.txt` is no longer an independent prose-only trust claim. Its TCB rows are
copied verbatim from the authoritative machine-readable
`phil.release-package`, with explanatory prose only around them.

The package smoke requires the two sets of TCB rows to match exactly and
requires exactly the four declared Phase-1 distribution trust kinds.

## Independent package smoke

The package-only smoke verifies, without repository state:

- every file against `SHA256SUMS`;
- exact release ID syntax;
- build metadata against the internal release record;
- exact target and source commit;
- exact packaged `philc` digest;
- exact frozen handoff-manifest digest;
- exact human/machine TCB correspondence;
- mandatory explicit target selection;
- rejection of an unknown target;
- accepted LLVM emission with exact target triple/data layout;
- scalar binding preservation; and
- rejection of invalid source.

The permanent INT-011 Linux workflow additionally verifies the external archive
binding against the actual tarball and the extracted package manifest before
running the package smoke in a fresh consumer directory.

## Remaining INT-011 work

After this Linux identity slice lands, INT-011 still requires:

1. the same distribution identity for native Apple Silicon;
2. Developer ID signing of the exact shipped `philc` executable;
3. Apple notarization and a quarantine-intact launch/smoke;
4. composition of immutable Linux/Darwin release assets; and
5. final GitHub Release publication bound to the exact source commit and release
   records.

Those are distribution/deployment closures. They do not reopen the frozen
Phase-1 language semantics.
