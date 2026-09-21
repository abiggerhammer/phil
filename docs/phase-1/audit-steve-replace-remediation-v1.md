# PHIL-AUD-STEVE-REPLACE-001 remediation

## Audit identity

- Finding: `PHIL-AUD-STEVE-REPLACE-001`
- Event: `PHIL-AUDIT-20260921-STEVE-HOST-FILESYSTEM`
- Audited frozen source: `a9f2c745686d8ae1b923e21045554f4864956e76`
- Public host adapter: `runtime/phase1/StevePublicMain.hs`
- Public package path: `scripts/release/build-steve-phase1-package.sh`

This slice remediates the host realization of the existing IO-FS replacement
contract. It does not add crash durability, sandbox/root-confinement guarantees,
or new proof/Certified status.

## Root cause

The public GET launcher previously implemented replacement with:

`ByteString.writeFile destination bytes`

wrapped in an ignored `IOException`. Opening an existing destination in write
mode may truncate it before a later write fails. A missing destination may be
created before the failure. That violates the existing process-observable
failure contract, where failed replacement preserves the exact prior state.

The digest check before publication was not the missing guard: the same
second-read bytes were already checked and passed to replacement. The defect
was publication semantics after admission.

## Repair

The public launcher now delegates destination publication to
`SteveUserFile.replaceFilePreservingFailure`.

The host adapter:

1. creates a unique staged file in the destination directory;
2. applies the existing destination's POSIX mode bits when replacing an
   existing file;
3. otherwise uses ordinary host default creation permissions/umask;
4. writes the complete candidate bytes to the staged handle;
5. successfully closes the staged handle;
6. only then publishes with a same-directory rename; and
7. on any pre-publication `IOException`, closes/unlinks the stage and returns
   failure without modifying the destination.

The final rename is the publication point. No fallible cleanup or metadata
operation is performed after a successful rename, so a successfully published
state is not subsequently reported as an unchanged-state failure.

The write and close phases run with normal interruptibility; the publication
step is performed in a masked region. Asynchronous process interruption and
crash durability remain separate from this process-observable failure contract.

## Scope boundaries

This repair does not claim:

- protection against a symlinked parent path;
- a complete leaf-symlink or hardlink alias policy;
- crash/power-loss durability;
- a concrete maximum read size;
- CAS in-process handle cleanup closure; or
- an independently acknowledged PUT installation result.

Those remain the separate questions recorded by Astra's audit ledger.

## Regression evidence

### Focused host-adapter replay

`scripts/ci/test-steve-replace-failure.sh` compiles the real staged host
adapter and exercises it under isolated Linux `RLIMIT_FSIZE` constraints:

- ordinary successful replacement publishes exact bytes;
- successful replacement preserves an existing mode control;
- an empty replacement succeeds under a zero file-size limit;
- R01: zero-capacity write failure preserves existing sentinel bytes;
- R02: partial staged write failure preserves existing sentinel bytes;
- R03: failed replacement of an absent path preserves absence;
- unrelated state remains unchanged; and
- no staged temporary file survives the failure cases.

The worker returns explicit `published` versus `preserved` status so the
tests do not infer the publication result merely from process exit.

### Packaged public launcher replay

The ordinary Steve package smoke now runs R01-R03 against the actual unpacked
`bin/steve` on Linux after a valid CAS object has passed Steve's normal GET
path. The smoke still retains its existing PUT/GET success and corrupt-CAS
sentinel controls.

The dedicated audit workflow builds the same distributable Steve archive,
unpacks it, runs its packaged smoke, and requires both the original smoke marker
and the new `PHIL-AUD-STEVE-REPLACE-001` marker.

## Assurance boundary

A green exact-head replay establishes the implementation/public-package
failure-preservation slice for this finding. The normalized filesystem theorem
remains a model-side authority whose native correspondence depends on this host
realization; no theorem is promoted or modified here.

Original-vs-repaired binary characterization, final frozen-snapshot delta
review, and the other open Steve host-policy questions remain separate audit
work.
