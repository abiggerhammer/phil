# Rocq proof certification

Phil distinguishes a proof that merely compiles in CI from a proof-assistant result that can be selected as certification authority.

The first certified specimen is `PHIL-CORE-SCALAR-001` in `proof/Phil/Core/Scalar.v`.

The certification adapter produces a canonical `phil-rocq-proof-certificate/v1` record that binds:

- the exact Phil obligation revision and claim digest;
- the exact checked `.v` source digest;
- the exact compiled `.vo` digest produced by Rocq 9.2.0;
- the theorem names used to justify the obligation;
- the checker/certificate profile;
- the residual trust boundary.

That certificate is itself content-addressed and selected in an ADR-010 assurance manifest as `ProofAssistantTheorem` evidence. `verifyManifest` must accept the exact artifact digest before the obligation is certified.

The proof workflow compiles the full Rocq corpus in the pinned `rocq/rocq-prover:9.2.0` container, uploads the exact `Scalar.v`/`Scalar.vo` pair, and passes those bytes to the Phil certification executable. The resulting certificate is retained as a workflow artifact.

## Explicit trust boundary

This slice does not claim that Phil independently reimplements or replays the Rocq kernel. Rocq kernel/toolchain correctness remains external trust. The reviewed correspondence from the human-facing `PHIL-CORE-SCALAR-001` claim to the normalized theorem family in `Scalar.v` also remains explicit rather than being hidden as an automatic semantic-equivalence claim.

The intended progression is:

```text
Rocq source
-> pinned Rocq kernel check
-> exact compiled proof object
-> Phil canonical proof certificate
-> ProofAssistantTheorem evidence
-> assurance manifest closure
```
