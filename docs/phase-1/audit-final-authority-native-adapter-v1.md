# D-ARTIFACT-MANIFEST-REFLECTION-01 — bounded native final-authority projection

**Date:** 2026-11-05. **Audit lineage:** NR-D06 / D-ARTIFACT-MANIFEST-REFLECTION-01. **Predecessor:** [#1575](https://github.com/abiggerhammer/phil/pull/1575), bounded StageClosure/INT-005 caller reconciliation.

## Problem

The Rocq `FixedFinalAuthorityAdapter` models a valid final-artifact composition only if an independently accepted native manifest, native stage and accepted source assurance are projected faithfully into the proof's distinct identity coordinates. A model made from stage values alone could appear to satisfy the theorem without establishing a relation to the actual native authority. Previous correspondence proofs correctly kept this premise explicit.

In current native Haskell, `AssuranceManifest` binds architecture/core/implementation/target/compilation/lowering/scope but **does not contain** `GenericApplicationAssurance` or its `GenericApplicationIdentity`. It is therefore unsound to synthesize the semantic proof's source-assurance identity from the manifest digest or from a stage.

## New native boundary

`Phil.Verification.FinalAuthorityAdapter` exposes `bindNativeFinalAuthority`:

- Accepts only **opaque already accepted** `CertifiedApplicationArtifact` (VER-010 source + StageClosure) and `CertifiedReleaseArtifact` (INT-005 manifest + stage + LLVM + trust declarations).
- Requires *full equality of the independently retained StageClosure objects*, not only a rev string or coincidentally matching digest.
- Requires an independently supplied `ExpectedSourceManifestAssociation` whose exact `GenericApplicationIdentity` and `manifestId` both match the separately accepted inputs. This association is **a caller-supplied assertion, not a certified proof of who selected it**. Its authenticity remains a distinct accepting/producer obligation.
- Uses the actual retained concrete StageClosure to extract subject, instance, realization, **normalized** Systems revision, **common** Phase-1 StageContract revision, and **closed** contract revision, while taking the raw Systems digest and lowering root from the same retained concrete artifact. Requires actual manifest raw digest/root equality again as a defensive crosscheck.
- Returns an opaque `NativeFinalAuthority` with read-only projections. It cannot be fabricated through a record update or public constructor.

This is a real native projection of accepted source/release objects into distinct identity domains, but it is **not an extraction of Rocq nat-valued model records** and does not produce `FixedFinalAuthorityAdapter` proofs.

## Positive and negative replay

The existing INT-005 test fixture now creates one genuine accepted source application through the VER-009 constructors and pairs it with the independently certified Upload and Steve release witnesses. It requires every projected native coordinate to equal the separately selected source or stage value.

Negative controls reject:
1. an independently certified release paired with a different accepted StageClosure;
2. a wrong externally supplied source application identity;
3. a wrong externally supplied final manifest identity.

The dedicated workflow builds the Haskell library with warnings fatal, typechecks and executes the native caller controls, reruns VER-010/SYS-020 controls, and recompiles the existing final-manifest fixed-adapter + certification Rocq chain with `Print Assumptions` and recorded identities.

## Scope and remaining obligations

This is a **bounded implementation correspondence adapter**, not the completion of the full semantic `FinalArtifactCertified` native correspondence theorem. In particular:

- No native source-identity field currently exists in the independently accepted manifest, and the supplied `ExpectedSourceManifestAssociation` is not independently certified by the new module. A competent producer/source-to-manifest binding or exact accepted source derivation is still needed.
- Haskell `Digest` / `Text` / stage revision representations are not magically injected into Rocq `nat` identities, and `NativeFinalAuthority` is not a theorem witness.
- Rich assurance/assumption/erasure producer-to-consumer binding, conditional native-to-model reflection and source preservation beyond the existing accepted interfaces remain separate.
- No release-byte revalidation, final candidate or independent sign-off is claimed. LLVM and runtime/provider trust remain unchanged.

The historical NR-D06 and independent September artifacts remain immutable. **This PR must not be described as certifying all of Phase 1.**
