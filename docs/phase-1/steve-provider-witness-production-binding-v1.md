# Steve provider witness production binding v1

This slice production-binds `PHIL-PROV-STEVE-WITNESS-001` to the exact executable kernel staged by #722.

## Exact kernel

Fresh Rocq 9.2 extraction of `proof/Phil/Core/SteveProviderQualificationWitnessImplementationExtraction.v` must produce `SteveProviderQualificationWitnessKernel.hs` exactly:

- size: 1717 bytes;
- SHA-256: `f13bc891587300ab3f7d05ff1b40f72103e4a0bc854995f3f49d987b39d19214`;
- checked-in copies: `generated/SteveProviderQualificationWitnessKernel.hs` and `src/SteveProviderQualificationWitnessKernel.hs`;
- both checked-in copies must compare byte-for-byte with fresh extraction.

The kernel owns the conjunction of the eleven representation-neutral witness facts staged by #722:

1. both Steve providers are admitted;
2. the Digest witness retains its exact stable subject;
3. the Digest scoped-borrow observation maps to that stable subject;
4. Digest candidate bytes remain borrowed and unconsumed;
5. Blob install preserves its candidate borrow on all three public outcomes;
6. Blob state, law, lifecycle, and authority qualification layers are present;
7. the Blob no-replace law rejects a second installed event;
8. Blob partial publication is forbidden;
9. Blob overwrite/delete authority is explicit and dispositioned;
10. Digest and Blob obligation manifests close exactly; and
11. claim conditions remain explicit in evidence and admission, including the Digest SHA-256 semantic-profile condition.

## Production boundary

`materializeSteveProviderQualifications` remains native-first. It still constructs DigestProvider and BlobProvider through the existing implementation-refined provider semantic, evidence, state, law, lifecycle, authority, and qualification-identity checkers. Their detailed native diagnostics retain precedence.

Only after both native materializers succeed does the function reflect the eleven facts from the returned checked artifacts and call `decideSteveProviderQualificationWitnessByFacts`. A kernel rejection converts that otherwise successful materialization into `SteveProviderQualificationError`; handwritten code cannot convert any native or kernel rejection into acceptance.

The negative Blob facts are not constants in the bridge: production reruns the existing provider-law checker on the forbidden double-installed trace and the provider-lifecycle checker on an injected partial-publication observation. This keeps those facts rooted in the already implementation-refined generic provider machinery.

## Regression pressure

The production gate reruns:

- #722's twelve direct extracted-kernel controls;
- the production materialization controls;
- the unchanged eleven-case PROV-016 Steve provider corpus; and
- strict `-Wall -Werror` typechecks of the exact kernel, bound materializer, and both harnesses.

## Explicit residual boundaries

This binding does **not** prove SHA-256 cryptographic correctness, filesystem/object-store behavior, crash/interference truth, completeness of the Blob state/law/lifecycle/interruption model, canonical identity construction, or complete ArchitectureRealization / Systems / StageContract integration. Concrete Haskell `Text`/`Map`/`Set` representation, finite enumeration, Rocq extraction/toolchain correctness, GHC/runtime correctness, and the truth/completeness of external provider evidence remain explicit boundaries.

`PHIL-PROV-STEVE-001` remains a separate aggregate row; this slice closes only the concrete bounded provider witness `PHIL-PROV-STEVE-WITNESS-001`.
