# Phase 1 provider replacement implementation refinement

This staging tranche extracts the bounded semantic decision surface already Certified by `PHIL-PROV-REPLACE-001`. Production is intentionally unchanged.

## Certified surface

`ProviderReplacementQualification.v` requires two independently admitted replacement sides to preserve the public interface, provider occurrence, and exact `InstanceRevision`; change semantic subject, `RealizationRevision`, claim, evidence, and admission lineage; scope every actually shared evidence reference explicitly; and reject reuse justifications for evidence that is not actually shared. Every reuse record must name the exact reference, exact prior and replacement claim revisions, and a nonempty validity scope.

The Haskell checker already implements the same ordered guard chain after independently validating both admission identities.

## Extracted decisions

`ProviderReplacementQualificationImplementation.v` reflects the native boundary into two finite Boolean decisions:

- `decideProviderReplacementByFacts` owns acceptance/rejection for admission status, fixed architecture coordinates, fresh realization/qualification lineage, complete shared-evidence scoping, and absence of spurious reuse; and
- `decideProviderReplacementReuseByFacts` owns exact reuse-reference, prior-claim, replacement-claim, and validity-scope checks.

The correspondence lemmas prove that acceptance requires every reflected Certified fact and that each first failing invariant has the same precedence as the production checker.

## Native bridge foundations

The extracted kernel does not own:

- correctness of `checkQualificationAdmissionIdentity` for either replacement side;
- `Text`, `Map`, or `Set` representation and traversal;
- construction or equality of concrete interface/instance/realization/claim/evidence/admission revisions;
- enumeration of evidence references from qualification evidence;
- correctness of shared-reference intersection or reuse-plan key-set difference; or
- the reflection from those concrete native facts to the Boolean inputs.

These remain explicit implementation/correspondence foundations. The kernel owns only the semantic result after those facts have been reflected.

## Validation

The dedicated workflow:

1. recompiles the existing Certified provider-replacement model;
2. compiles the implementation correspondence;
3. fresh-extracts the Haskell decision kernel;
4. strict-typechecks it under `-Wall -Werror`;
5. executes 18 direct controls covering acceptance and every ordered replacement/reuse rejection;
6. strict-typechecks the unchanged production checker and unchanged ARCH-010/PROV-015 pressure corpus; and
7. reruns all 12 existing provider-replacement/architecture-composition cases unchanged.

A green staging run is mechanized correspondence evidence only. `PHIL-PROV-REPLACE-001` remains `Discharged / Certified` until a separate closeout checks in the exact extracted kernel and routes production decisions through it.
