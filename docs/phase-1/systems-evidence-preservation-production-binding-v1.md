# Systems evidence preservation production binding v1

`PHIL-SYS-EVID-001` was already Certified and #524 staged its representation-neutral executable decision surface. This closeout binds production SYS-012/SYS-013 verification to the exact staged kernel while preserving the existing concrete representations, error payloads, and regression corpus.

## Exact kernel

The exact Rocq extraction harvested from #524 is checked in at:

- `generated/SystemsEvidencePreservationKernel.hs`
- SHA-256 `60611b8457f9f6c91941a5e7970e7714c807dab492cca228a0da9b690a0a1852`

`src/SystemsEvidencePreservationKernel.hs` is the strict production mirror: exactly the extracted bytes prefixed by the module-local `-Wno-unused-imports` pragma required for Rocq's generated qualified `Prelude` import.

The dedicated production-binding workflow fresh-extracts under Rocq 9.2.0, asserts the staged SHA, byte-compares the raw artifact, mechanically derives and byte-compares the strict production mirror, then validates the bound Haskell paths.

## SYS-011 predecessor

SYS-011 is not reimplemented here. `Phil.Systems.EvidenceSubjectTransfer` already routes its exact subject-transfer decisions through the production-bound `BoundarySubjectKernel`. The cumulative SYS-EVID classifier treats that accepted predecessor as the SYS-011 input.

## SYS-012 production binding

`Phil.Systems.EvidenceErasure` retains native `Text`/`Map`/`Set` lookup, enumeration, stage-revision construction, and exact diagnostic payload recovery. The extracted kernel now selects the Certified normalized decision class for the concrete facts that the stage carries:

- exact source-fact/subject evidence binding;
- exact discharge-evidence/subject binding;
- nonempty erased-representation identity;
- explicit last semantic use;
- explicit no-later-consumer basis;
- well-formed optional successor-invariant revision;
- well-formed optional runtime-residue-change revision;
- well-formed optional cost-change revision; and
- later-consumer safety/closure.

The Assurance erasure-use input is an explicit already-Certified predecessor fact from `PHIL-ASSURE-USE-001`. This concrete stage does not carry the full `AssuranceUseContext`/selected-evidence object, so it passes that predecessor as accepted rather than inventing a second native authority verifier.

When a native failing check is mapped to a Certified decision input, production first asks the exact kernel for the normalized class and then returns the existing detailed native error. Any impossible disagreement between the supplied fact position and the kernel's selected class fails closed as a kernel invariant error.

## SYS-013 production binding

`Phil.Systems.AssumptionDependency` keeps native map/set derivation and detailed mismatch payloads while routing the normalized Certified gates through the extracted kernel:

- exact required-assumption/registry domain;
- nonempty validity-scope revision;
- exact forward consumer domain and assumption sets;
- exact registered validity scope on forward edges; and
- exact reverse domain and consumer sets.

`PHIL-ASSURE-ASSUME-001` authority remains an explicit Certified predecessor fact. The concrete SYS-013 registry stores only the stable assumption key and validity-scope revision, not the authority/content-digest/selection context required to re-run that Assurance verifier locally.

The cumulative extracted classifier is used at the SYS-012 predecessor seam and at successful SYS-011--013 completion. Subject-transfer failure ownership remains with the already-bound SYS-011 predecessor; erasure failure ownership remains with SYS-012; assumption failure ownership remains with SYS-013.

## Residual boundary

This closeout does not claim that Rocq proves:

- Haskell `Text`, `Map`, `Set`, list, key, or revision representations;
- derivation/enumeration of source facts, subjects, consumers, or assumption maps;
- concrete `canonicalSemanticForm` encoding or stage revision construction;
- the truth of external Assurance evidence beyond the already-Certified predecessor gates;
- exact diagnostic text/payload construction;
- runtime/backend behavior; or
- GHC/Rocq/extraction/toolchain correctness.

Those remain the documented finite correspondence/evidence/TCB boundary. What becomes mechanically production-bound here is the Certified normalized SYS-012/SYS-013 decision structure over those reflected facts.

## Closeout gate

Before `PHIL-SYS-EVID-001` may move from `Discharged / Certified` to `Discharged / Implementation Refined`, the production-binding workflow must be green on the exact PR head and must demonstrate:

1. fresh Rocq extraction at the staged SHA;
2. byte-identical checked-in raw and strict kernels;
3. strict compilation of the bound SYS-012/SYS-013 production modules;
4. direct execution of the extracted 22-control decision harness against the production kernel; and
5. unchanged success of the existing 36-case SYS-011--013 correspondence corpus.
