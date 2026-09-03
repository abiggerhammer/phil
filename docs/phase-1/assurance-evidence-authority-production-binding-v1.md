# Assurance evidence authority production binding v1

This closes the production-binding half of `PHIL-ASSURE-EVID-001`.

The exact Rocq-extracted `AssuranceEvidenceAuthorityKernel.hs` staged by #638 is checked in byte-identically under both `generated/` and `src/`. Production `Phil.Assurance.Verify` keeps its existing concrete checks and diagnostics, then requires the extracted gate to accept the same facts before an artifact-backed or `RuntimeEnforced` evidence entry can pass.

## Bound decisions

Artifact-backed evidence is admitted only after the production verifier has established:

- an artifact is declared;
- the exact artifact reference is present in trusted availability;
- its declared digest equals the trusted digest.

`RuntimeEnforced` evidence is admitted only after production has established:

- a runtime mechanism is present;
- the mechanism's required descriptive fields are complete;
- runtime residue is nonempty;
- at least one cost reference is present;
- every declared cost reference is known in the selected verification context.

The extracted gate runs after the existing native checks. Therefore existing diagnostic ordering and payloads are preserved. A native-success/kernel-reject disagreement fails closed with `EvidenceAuthorityKernelDisagreement`; it cannot turn any kernel rejection into success.

## Explicit boundaries

This binding does not mechanize concrete Haskell representation identity, `Map`/`Set` behavior, trusted-artifact lookup, SHA-256 collision resistance, runtime-mechanism construction or semantic soundness, runtime-residue construction, known-cost-set construction, runtime implementation-artifact truth, external proof/test/translation truth, diagnostic payload construction, GHC/runtime correctness, or the Rocq extraction toolchain.

`Assumed` evidence is intentionally outside this slice and remains governed by the separate explicit assumption-authority boundary. `KernelChecked` evidence has no artifact/runtime gate and is unchanged.

The production workflow freshly re-extracts the kernel under Rocq 9.2.0, requires exact SHA-256 and byte identity for both checked-in copies, runs the direct extracted controls, runs production binding controls, and reruns the unchanged assurance corpus.
