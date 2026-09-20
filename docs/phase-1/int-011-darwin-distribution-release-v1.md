# Phase 1 INT-011 Darwin distribution release v1

## Purpose

This slice carries the canonical INT-011 standalone-distribution identity from
x86-64 Linux to native Apple Silicon macOS and adds the Apple deployment
closures required for a browser-downloadable command-line release.

The important ordering is:

1. build the native `philc` executable;
2. Developer-ID sign that exact executable;
3. compute the canonical distribution release identity from the **signed**
   executable bytes;
4. construct the package manifest and exact ZIP archive;
5. bind the archive to the internal release identity;
6. submit that exact archive to Apple notarization;
7. require notarization acceptance; and
8. launch the signed compiler with `com.apple.quarantine` still attached.

Signing therefore cannot be a post-processing step after release identity.
Developer ID changes the compiler bytes, and those final bytes are what the
machine-readable release record names.

## Shared distribution format

Darwin uses the same versioned internal and external records established by the
Linux INT-011 slice:

- `PHIL-PHASE1-DISTRIBUTION-RELEASE-V1`;
- `PHIL-PHASE1-DISTRIBUTION-ARCHIVE-V1`.

The internal record binds:

- package/version;
- target `aarch64-apple-darwin`;
- exact source commit;
- exact SHA-256 of the frozen INT-007 handoff root;
- exact SHA-256 of the Developer-ID-signed `philc`; and
- the complete residual distribution TCB.

The archive record binds:

- the internal distribution release ID;
- exact ZIP filename;
- exact ZIP SHA-256; and
- exact SHA-256 of the unpacked package `SHA256SUMS`.

No Darwin-specific alternate package identity is introduced.

## Darwin residual TCB

The required distribution trust-kind domain remains exactly the Phase-1 domain:

- compiler/checker;
- build toolchain;
- LLVM toolchain;
- target assumptions.

The Darwin profile specializes the latter boundaries to the conventional Apple
Silicon host toolchain and the Apple Silicon Darwin ABI/loader/Gatekeeper/runtime
assumptions. Developer-ID signing and notarization provide distribution
authenticity/deployment evidence; they do not turn those platform assumptions
into verified Phil semantics.

## Developer ID binding

The permanent workflow imports the Developer ID Application credential from the
existing `macos-release` environment, signs `bin/philc` with hardened runtime
and secure timestamp options, then requires:

- strict `codesign` verification;
- the exact expected Apple Team Identifier; and
- deployment floor `macOS 11.0`.

Only after those checks does the builder generate
`share/phil/phil.release-package`.

Consequently the compiler digest named by the INT-011 release record commits to
the actual code signature embedded in the shipped Mach-O bytes.

## Notarization

The signed ZIP is submitted through the existing bounded
`notarize-darwin-archive.sh` helper.

Submission and polling are separated. The submission ID and JSON response are
preserved with the exact archive, and the polling job requires an explicit
`Accepted` result before deployment assessment continues.

Notarization status is external Apple service evidence associated with the exact
submitted archive. It is not folded into the canonical compiler or archive
digest and therefore does not create a self-referential package identity.

## Quarantine-intact external smoke

After notarization acceptance, the exact preserved archive is extracted and its
INT-011 archive binding is rechecked against:

- the actual ZIP SHA-256;
- the internal release ID; and
- the extracted package-manifest SHA-256.

The workflow then:

1. strictly verifies the Developer-ID signature and Team Identifier;
2. attaches `com.apple.quarantine` to the shipped `philc`;
3. optionally records `spctl` diagnostics without treating app-bundle-oriented
   diagnostics as the sole CLI authority;
4. runs the complete package-only Phil smoke while quarantine remains present;
5. requires the quarantine attribute still to be present after successful
   launch.

The package smoke independently rechecks the frozen handoff digest, signed
compiler digest, source commit, target, BUILD-INFO bindings, human/machine TCB
correspondence, target-selection failure cases, accepted LLVM emission, scalar
binding preservation, and rejected-source behavior.

Removing quarantine, disabling Gatekeeper, or invoking an unsigned replacement
binary is not an admitted release procedure.

## Exit from this slice

This slice is complete when both Darwin workflow jobs are green:

- signed package build + exact notarization submission;
- accepted notarization + exact archive/release verification +
  quarantine-intact package smoke.

After that, the remaining INT-011 work is release-bundle composition and
immutable GitHub Release publication of the certified Linux and Darwin assets.
