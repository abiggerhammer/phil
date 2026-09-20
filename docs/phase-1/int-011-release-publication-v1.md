# Phase 1 INT-011 final release publication v1

## Purpose

This slice closes INT-011 by composing the independently certified Linux and
Apple Silicon distributions into one machine-readable Phase-1 publication
record and publishing exactly those assets under one immutable GitHub Release
tag.

The release tag is:

`phil-v0.1.0-phase1`

The package version is:

`0.1.0-phase1`

## Why there is a top-level bundle record

The Linux and Darwin packages already have independent internal distribution
identities and external archive bindings. Publication adds one more authority
boundary: the claim that **these two platform artifacts are the two official
distributions of one Phase-1 source commit and one frozen INT-007 handoff
root**.

That claim is represented by:

`phil-0.1.0-phase1.release-bundle`

with header:

```text
PHIL-PHASE1-DISTRIBUTION-BUNDLE-V1
```

The bundle body records:

- bundle format revision;
- package name/version;
- exact source commit;
- exact frozen Phase-1 handoff-manifest SHA-256;
- one platform record for `x86_64-unknown-linux-gnu`;
- one platform record for `aarch64-apple-darwin`.

Each platform record binds:

- internal distribution release ID;
- exact packaged compiler SHA-256;
- external archive-binding ID;
- archive filename and SHA-256;
- exact SHA-256 of the external `.release` record;
- package `SHA256SUMS` digest.

The Darwin record additionally binds:

- Apple notarization submission ID;
- required status `Accepted`; and
- SHA-256 of the exact Apple notarization-info JSON published with the release.

The bundle ID is SHA-256 of the canonical bundle body. A separate
`.release-bundle.sha256` file content-addresses the complete rendered bundle.

## Independent composition checks

The release-bundle composer does not trust the platform artifact filenames or
CI job names as authority. It independently:

1. verifies archive and `.release` checksum sidecars;
2. reads the internal distribution release record directly from each archive;
3. recomputes each internal release ID from its canonical body;
4. requires exactly the four Phase-1 distribution TCB kinds;
5. verifies the packaged `philc` digest against the internal record;
6. verifies the packaged frozen handoff-manifest digest;
7. verifies every file in each package against the package `SHA256SUMS`;
8. recomputes each archive-binding ID from its canonical body;
9. checks archive digest, archive name, internal release ID, and package-manifest
   digest against that archive binding;
10. requires both platforms to name the workflow's exact source commit;
11. requires both platforms to name the same frozen INT-007 handoff root;
12. requires Apple notarization status `Accepted` and an exact submission-ID
    match between the preserved ID file and Apple info response.

Only after those checks does it construct the cross-platform bundle identity.

## Published asset set

The immutable GitHub Release contains exactly the following eleven assets.

Linux:

- `phil-0.1.0-phase1-x86_64-linux.tar.gz`
- `phil-0.1.0-phase1-x86_64-linux.tar.gz.sha256`
- `phil-0.1.0-phase1-x86_64-linux.tar.gz.release`
- `phil-0.1.0-phase1-x86_64-linux.tar.gz.release.sha256`

Apple Silicon:

- `phil-0.1.0-phase1-aarch64-apple-darwin.zip`
- `phil-0.1.0-phase1-aarch64-apple-darwin.zip.sha256`
- `phil-0.1.0-phase1-aarch64-apple-darwin.zip.release`
- `phil-0.1.0-phase1-aarch64-apple-darwin.zip.release.sha256`
- `phil-0.1.0-phase1-aarch64-apple-darwin.zip.notary-info.json`

Cross-platform:

- `phil-0.1.0-phase1.release-bundle`
- `phil-0.1.0-phase1.release-bundle.sha256`

GitHub's automatically generated source archives are not release assets and are
not part of the INT-011 asset-set equality check.

## Publication transaction

On a pull request the permanent workflow performs the complete platform builds,
notarization, package smoke tests, bundle composition, and asset-set preparation,
but does not publish.

On the merge commit pushed to `main`, the same workflow rebuilds both platform
artifacts from that exact commit and then:

1. creates `phil-v0.1.0-phase1` as a draft release targeting the exact
   `GITHUB_SHA`;
2. uploads the eleven exact assets;
3. requires the release asset-name set to equal the declared set exactly;
4. publishes the release;
5. requires the Git tag to resolve to the exact source commit.

No publication step is allowed to move an existing published tag.

## Signing timestamps and immutable reruns

Developer-ID signing uses a secure timestamp. Therefore a later Darwin rebuild
from the same Git commit is not required to reproduce the exact signed Mach-O or
ZIP bytes of the already published release.

That is why a published release is immutable rather than rebuilt-and-clobbered.

If `phil-v0.1.0-phase1` already exists:

- a different tag commit is a hard failure and requires a new package version;
- the exact published asset-name set must still match;
- the existing published release bundle and its checksum are verified;
- its machine-readable source commit must still equal the tag commit.

A later workflow run may build fresh staging evidence, but it cannot replace the
published signed artifacts merely because the source commit is unchanged.

## INT-011 exit condition

INT-011 is complete when the publication workflow is green on the merge commit
and all of the following are true:

- Linux package certification and package-only smoke pass;
- Darwin Developer-ID signing passes;
- Apple notarization is accepted;
- quarantine-intact Darwin package smoke passes;
- the canonical cross-platform bundle composes successfully;
- the immutable GitHub Release is public;
- its exact eleven-asset set is present; and
- `phil-v0.1.0-phase1` resolves to the exact commit recorded by both platform
  releases and the top-level bundle.

At that point the Phase-1 repository has a browser-downloadable standalone
compiler release whose distribution claims are content-bound to the frozen
Phase-1 handoff and whose remaining trust boundary is explicit rather than
implicit.
