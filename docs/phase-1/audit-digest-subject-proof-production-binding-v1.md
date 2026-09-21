# PHIL-AUD-DIGEST-SUBJECT-001 — production proof correspondence

This closes the proof/production-binding gap left by the implementation remediation.

PR #1276 staged the normalized subject-carrying proof and extracted
`SurfaceDigestSubjectKernel.hs`.

Exact staged kernel:

- size: **1,890 bytes**
- SHA-256: `9994e5675c20fbad9f0e2aefa66907817ab3bd9db837356b25bc55b878f5023e`
- staging artifact ID: `10656052277`
- artifact digest: `sha256:3a835eab11c957016876306f7fccb9be6d5361d058347c181bffdb96674e7764`

`generated/SurfaceDigestSubjectKernel.hs` and
`src/SurfaceDigestSubjectKernel.hs` are byte-identical copies.

## Production binding

The existing native `evalValidate` checks still run first and retain their exact
source-facing diagnostics. On native success, the actual checked Begin `Name`
and stable byte-owner `RefTerm` are passed to
`certifyDigestSubject`.

The certification bridge accepts only when the extracted kernel:

1. returns an accepted decision;
2. returns exactly the same Begin subject; and
3. returns exactly the same stable owner.

The final `DigestMatches` proposition is constructed from those
kernel-returned subjects. A kernel rejection or any subject substitution fails
closed before evidence is produced.

The production harness injects both rejection and subject-substitution decisions
to demonstrate the fail-closed boundary independently of the real extracted
kernel.

## Closure

A fully green exact-head merge closes the proof-correspondence portion of
`PHIL-AUD-DIGEST-SUBJECT-001`: the repaired public producer is mechanically
connected to the theorem that acceptance preserves the exact checked subjects.

Digest cryptography, generic validator semantics, parser correctness, concrete
Haskell representation, and downstream Systems/LLVM realization remain
separate boundaries.
