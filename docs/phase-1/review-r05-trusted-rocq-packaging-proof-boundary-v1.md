# PHIL-P1-REVIEW-R05 proof boundary

This slice certifies Astra Review R05: Phil's public Rocq certification command is an explicit **trusted-packaging boundary**, not an in-process Rocq verifier.

The authority rule is deliberately narrow:

- the public command refuses the legacy unqualified invocation;
- packaging requires the explicit `--trusted-checked-inputs` acknowledgement;
- the source must name the expected obligation and theorem declarations;
- the certificate content-binds both the source and compiled proof artifacts;
- the certificate checker profile says `trusted-packaging`; and
- the emitted assurance evidence says successful Rocq checking is an explicit caller precondition.

The proof intentionally does **not** claim that `packageTrustedRocqProof` authenticates Rocq or validates arbitrary `.vo` bytes. It does not. Successful Rocq checking remains a producer-side premise outside the packaging adapter. The proof makes that negative boundary explicit so packaging success cannot be misread as an independent kernel check.

The concrete Haskell authority is split between `app/RocqScalarCertificationMain.hs` and `src/Phil/Assurance/Rocq.hs`. The CLI gates entry on `--trusted-checked-inputs`; the packager checks the source profile/theorem names, hashes source and compiled bytes into the certificate, labels the checker profile as externally checked trusted packaging, emits `ProofAssistantTheorem` evidence whose checker names the caller precondition, and closes the resulting assurance manifest.

The dedicated correspondence gate replays both the ordinary Rocq-certification regression and the exact public CLI boundary with deliberately invalid compiled bytes: the unqualified invocation must reject, while the explicitly trusted packaging invocation may package those bytes and must visibly retain the `trusted-packaging` label. That asymmetry is intentional evidence of the boundary, not a proof-object validator.

Rocq kernel/toolchain correctness, the producer workflow that actually runs Rocq before packaging, command-line argument plumbing, filesystem integrity, GHC/runtime correctness, and correspondence from concrete certificate text to the normalized proof model remain explicit trust boundaries.
