# Phase 1 target runtime primitive implementation refinement v1

Status: machine implementation-refinement staging for `PHIL-TARGET-RUNTIME-PRIM-001`.

## Certified boundary

`proof/Phil/Core/RuntimePrimitiveIdentity.v` gives the target-neutral runtime-primitive identity rule. A successful verification has exactly two semantic facts:

1. the actual target-entry identity is the entry selected by the exact physical primitive identity together with the exact target profile/signature; and
2. assurance revision, evidence identity, assurance-use identity, and claim count are not encoded into that target-entry identity.

The theorem intentionally leaves the target-entry representation abstract. An LLVM linker symbol, WebAssembly import/function/table identity, VM opcode/precompile identity, SBF syscall/CPI target, or another backend mechanism belongs to a target-specific refinement and is not imported into Phil Core or generic Systems semantics.

## Machine decision surface

`RuntimePrimitiveIdentityImplementation.v` retains those two facts without strengthening the theorem:

```text
decideRuntimePrimitiveIdentityByFacts(
  physical_profile_exact,
  no_assurance_encoding
)
```

The decision accepts iff both facts hold. The implementation proof establishes soundness and completeness for the exact Certified `RuntimePrimitiveIdentityVerificationSuccess` record. Fresh Rocq extraction emits `RuntimePrimitiveIdentityKernel.hs`.

The direct correspondence harness exercises all three Boolean classes: exact acceptance, entry drift rejection, and assurance-derived identity rejection.

## Current production representation

Production SYS-016 is already target-neutral in `Phil.Systems.RuntimePrimitiveReuse`.

The existing checked `RuntimeSiteRef` carries separate coordinates for runtime semantics/evidence and for the reusable lower-stage implementation/profile token. The bounded SYS-016 representation interprets:

```text
RuntimePrimitiveProfileRef(runtimeSiteCostRef)
```

as the selected implementation-family/profile coordinate. `deriveRuntimePrimitiveSiteBindings` constructs the profile from that coordinate alone. Runtime-site revision/evidence, claim identities, semantic subjects, and site-owned physical cost identity are retained independently and are checked not to collapse under primitive reuse.

This typed-coordinate separation is the concrete correspondence foundation for the Certified no-assurance-encoding fact. It is **not** a claim that arbitrary Text coincidence can prove provenance. A later richer schema may split implementation/profile and cost-model references into distinct first-class fields without changing the invariant: assurance metadata must not become primitive-entry identity authority.

## Staging boundary

This PR does not change `Phil.Systems.RuntimePrimitiveReuse` or any production acceptance path. It only adds the executable Certified decision surface and checks it against the unchanged SYS-016 implementation/corpus.

Evidence therefore remains **Certified** until a production-binding slice:

- freshly extracts and byte-binds the exact kernel;
- preserves native SYS-016 diagnostic precedence;
- independently reflects the exact primitive/profile projection fact and the typed-coordinate no-assurance-encoding fact;
- fails closed on any native-success/kernel-reject disagreement; and
- reruns the implementation-refined Systems Runtime Graph and its RuntimeCarrier/StorageCost consumers.

## Explicit retained boundaries

The following remain outside this target-neutral identity theorem:

- truth/provenance of the selected `runtimeSiteCostRef` as the implementation-family/profile input;
- concrete `Text`, `Map`, and `Set` representation and finite traversal;
- construction and verification of the predecessor SYS-015 runtime-site graph;
- target-specific linker/import/opcode/table/calling semantics;
- scheduler, runtime, IPC, device, or platform correctness;
- physical cost-model truth and quantitative values;
- target-specific call multiplicity;
- Rocq extraction/toolchain, GHC, and runtime correctness.

No fairness, progress, performance, linker, ABI, or backend execution claim is added by this staging slice.
