# Phase 1 provider replacement production binding

This closeout binds the executable decision surface staged by `PHIL-PROV-REPLACE-001` directly into the production provider-replacement checker.

## Certified kernel

`src/ProviderReplacementQualificationKernel.hs` is the byte-for-byte Rocq extraction harvested from #404. Its staging SHA-256 is:

`cc88e7fecf48e0a7813dbf1f3247ecefc3e960abff761bb6dfee65bc0b3cfd59`

The kernel owns two ordered semantic decisions:

- replacement-level admission, fixed architecture identity, fresh implementation/realization/qualification lineage, shared-evidence scoping, and absence of spurious reuse; and
- per-reuse exact reference, exact predecessor/replacement claim pair, and nonempty validity scope.

## Native bridge facts

Production still owns the concrete representation facts supplied to the kernel:

- independent predecessor and replacement qualification-admission checks;
- equality/difference of concrete interface, occurrence, instance, subject, realization, claim, evidence, and admission identities;
- finite `Map`/`Set` enumeration, intersection, membership, and difference for evidence references and reuse records; and
- `Text` emptiness for the concrete validity-scope revision.

The production checker reflects those facts into the extracted Boolean decision surface. Kernel outcomes are translated back into the existing public diagnostics; finite-map traversal, checked-result construction, and diagnostic payloads are unchanged.

The kernel's single `ProviderReplacementAdmissionRequired` outcome is refined back into the existing predecessor-first / replacement-second diagnostics by inspecting the two already-checked admission decisions. Reaching that kernel outcome when both admissions are accepted is an explicit fail-closed bridge mismatch.

## Verification

The dedicated production-binding workflow:

1. recompiles the Certified `ProviderReplacementQualification.v` model and implementation correspondence;
2. fresh-extracts `ProviderReplacementQualificationKernel.hs`;
3. byte-compares the fresh extraction with the checked-in production kernel and verifies the harvested SHA-256;
4. strict-typechecks the exact kernel under `-Wall -Werror`;
5. strict-builds the production package and strict-typechecks the bound replacement checker;
6. executes the 18 direct extracted-kernel controls unchanged;
7. strict-typechecks and reruns all 12 existing PROV-015 / ARCH-010 provider-replacement cases unchanged; and
8. records exact production source identities in a closeout artifact.

Package-publication metadata is not part of this implementation correspondence, so this workflow intentionally does not run `cabal check`.

A fully green exact-head run closes the bounded `PHIL-PROV-REPLACE-001` implementation correspondence. Architecture realization remains separately responsible for binding its own realization-construction plan.
