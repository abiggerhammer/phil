# Provider evidence production binding v1

This closeout binds the production `PHIL-PROV-EVIDENCE-001` checker to the exact Rocq-extracted decision surface staged by #416.

## Exact kernel

`src/ProviderEvidenceQualificationKernel.hs` is checked in byte-for-byte from the #416 extraction and must have SHA-256:

`5569956812f2c6a81e5b15f08fbc8fe92bd331f0e11efd378401b46fa7126997`

The production checker imports that exact module directly. No package-policy change is needed for this semantic binding: `phil-core.cabal` remains byte-identical, while the dedicated workflow strict-builds the ordinary production component and records the unchanged manifest hash alongside the bound sources. The workflow fresh-extracts the kernel from `ProviderEvidenceQualificationImplementationExtraction.v` and byte-compares the result before compiling production.

## Production-owned reflected facts

`Phil.Core.ProviderEvidenceQualification` still owns the concrete Haskell representation facts supplied to the extracted decisions:

- membership of the required operation in the already checked provider qualification;
- exact `ProviderOperationKey`, proposition-family, `[RefTerm]`, stable-subject, and validity equality;
- exact `ProviderEvidenceObservation` equality;
- exact mapped stable-subject equality; and
- concrete `Text`, `LoanScopeKey`, `RefTerm`, `Proposition`, and `Map` behavior.

Those are named native representation foundations, not silently promoted into the Rocq model.

## Extracted semantic decisions

The extracted kernel now owns the ordered evidence-specific semantic choice:

1. required operation is already qualified;
2. claimed operation is exact;
3. proposition family is exact;
4. semantic proposition parameters are exact;
5. stable proposition subject is exact;
6. validity contract is exact; and
7. subject mapping is admissible.

For subject mappings, production reflects facts into the exact extracted constructors:

- direct stable mapping accepts only an exact `StableEvidenceObservation mappedSubject` whose mapped subject is the proposition subject;
- checked observation-to-subject mapping checks exact observation before exact stable subject; and
- runtime coincidence always rejects.

The existing public diagnostics, checked-result fields, proposition materialization, and provider-lineage fields remain unchanged. Any impossible mismatch between an extracted result and the native constructor being translated fails closed.

## Composition boundary

The upstream provider semantic qualification is not duplicated here. `PHIL-PROV-QUAL-IMPL-001` already mechanically binds that semantic layer to its Certified Rocq model. This closeout consumes the resulting `CheckedProviderSemanticQualification` and binds only the evidence-specific suffix owned by `PHIL-PROV-EVIDENCE-001`.

This closeout does not prove proposition truth, SHA-256 correctness, truth of externally supplied observation mappings, generic consume/reconstruct evidence transport, qualification/admission lineage, Systems preservation, target realization, or final syntax.

## Exact-head verification

The existing registered workflow path now runs as `Phase 1 Provider Evidence Production Binding`. It:

1. rebuilds the Certified provider-evidence proof and implementation correspondence;
2. fresh-extracts the kernel and byte-compares it with `src/ProviderEvidenceQualificationKernel.hs`;
3. asserts the harvested `55699568…` SHA-256;
4. strict-compiles the checked-in kernel and production checker under `-Wall -Werror`;
5. strict-builds the ordinary production library/certifier path;
6. reruns all 14 direct extracted-kernel controls unchanged;
7. reruns the unchanged provider-semantic, PROV-010, and Steve provider corpora; and
8. records exact kernel, production checker, unchanged Cabal manifest, harness, corpus, and documentation hashes in a closeout artifact.

`cabal check` is deliberately outside this correspondence workflow because package-publication metadata is unrelated to this semantic obligation.
