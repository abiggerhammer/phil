# Phase 1 Target Runtime Primitive production binding v1

Status: production implementation refinement for `PHIL-TARGET-RUNTIME-PRIM-001`.

## Boundary

This slice binds the existing target-neutral Systems representation to the exact kernel extracted from `RuntimePrimitiveIdentityImplementation.v`.

The Certified success record has exactly two facts:

1. the selected target-neutral entry is exactly the one determined by the bounded physical-primitive/profile coordinate; and
2. assurance identity is not encoded into that entry.

The extracted production kernel therefore remains exactly:

```text
physical_profile_exact && no_assurance_encoding
```

It does not know about LLVM symbols, WebAssembly imports/tables, VM opcodes or precompiles, SBF syscall/CPI identities, calling conventions, scheduler state, runtime behavior, performance, or device identity.

## Bounded Systems representation

Phase 1 SYS-016 already uses:

```text
RuntimePrimitiveProfileRef(runtimeSiteCostRef)
```

as its reusable implementation-family/profile coordinate. The current bounded schema does not split physical primitive family and target profile into two separate first-class fields. The Certified relation permits that later refinement; this production bridge certifies the exact coordinate the current schema actually carries.

`targetRuntimePrimitiveEntry` is the target-neutral constructor for this bounded representation:

```text
RuntimeSiteRef -> RuntimePrimitiveProfileRef(runtimeSiteCostRef)
```

Only `runtimeSiteCostRef` is projected. `runtimeSiteRevision` and `runtimeSiteEvidence` are deliberately not inputs. Claim identities, semantic subjects, site multiplicity, and physical cost identities likewise remain outside the target-entry constructor and continue to be checked by SYS-015/SYS-016.

## Native-first production admission

`Phil.Systems.RuntimePrimitiveIdentityCertification` introduces an opaque `CertifiedRuntimePrimitiveStage`.

The only public constructor path is `certifyRuntimePrimitiveStage`:

1. run the existing `verifyRuntimePrimitiveStageBundle` SYS-016 verifier first;
2. traverse every exact primitive site in the accepted stage;
3. recover the exact predecessor `RuntimeSiteRef` for the same `RuntimeSiteKey`;
4. derive the target-neutral entry solely with `targetRuntimePrimitiveEntry`;
5. reflect the two Certified facts;
6. require the exact extracted kernel to accept them; and
7. store only the exact site-to-target-entry map behind the opaque certificate.

Native SYS-016 diagnostics therefore retain precedence. A relabeled primitive profile is rejected as `RuntimePrimitiveProfileMismatch` before it can be promoted into a certified target-neutral identity.

## No-assurance-encoding correspondence

The Rocq model represents “no assurance encoding” as an explicit success fact. In the current Haskell schema the corresponding production fact is structural: the target-neutral entry constructor projects only `runtimeSiteCostRef`.

The production controls mutate `runtimeSiteRevision` and `runtimeSiteEvidence` independently while holding `runtimeSiteCostRef` fixed and require the target-neutral entry to remain byte-for-byte/equality identical. This is a representation-correspondence claim, not a claim that arbitrary `Text` values have trustworthy provenance outside the checked SYS-015/SYS-016 construction path.

## Exact kernel identity

The checked-in production copies are byte-identical to the fresh Rocq extraction from #708:

- size: `386` bytes;
- SHA-256: `9ec11eff3177ae9606f551e20bd3fbe9051c44fe113e8ba8f57d9b80e6e55dc0`;
- the file ends with two newline bytes, preserved exactly.

CI freshly recompiles the Certified theorem and implementation surface, re-extracts the kernel, checks size and SHA-256, and compares it byte-for-byte with both checked-in production copies.

## Production controls

The dedicated production harness checks:

- upload's complete exact primitive-site domain certifies;
- Steve's empty primitive-site domain certifies vacuously without inventing a primitive;
- assurance revision changes alone cannot rename the target-neutral entry;
- assurance evidence changes alone cannot rename the target-neutral entry;
- native SYS-016 primitive/profile relabeling remains fail-closed before kernel admission;
- all-true exact kernel facts are accepted;
- physical/profile disagreement is rejected; and
- assurance-encoding disagreement is rejected.

The unchanged 18-case SYS-016 corpus is rerun under strict warnings, and the LLVM runtime-symbol refinement is recompiled as a downstream target-specific instance.

## Explicit residual boundaries

This production binding does **not** certify:

- a concrete LLVM/WebAssembly/EVM/SBF target-entry representation;
- calling convention, linker, table, instruction, syscall, or CPI correctness;
- target runtime implementation correctness;
- runtime progress, fairness, timing, or performance;
- a richer future split between primitive family, target profile, and cost-model references; or
- LLVM call multiplicity, which remains owned by the LLVM-specific refinement theorem.

Those remain target-profile or backend obligations. This slice closes only the target-neutral Haskell representation correspondence for `PHIL-TARGET-RUNTIME-PRIM-001`.
