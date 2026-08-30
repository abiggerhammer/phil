# PHIL-PROV-EVIDENCE-001 implementation refinement staging

This slice stages an executable, representation-neutral decision surface for the
already-Certified `PHIL-PROV-EVIDENCE-001` evidence-producer competence theorem.
It does not change production behavior.

## Certified decomposition

`ProviderEvidenceProducerCompetent` decomposes into:

1. an already-qualified provider implementation (`ProviderQualifies`);
2. presence of the required public operation;
3. exact claimed operation;
4. exact proposition family;
5. exact proposition parameters;
6. exact stable proposition subject;
7. exact validity contract; and
8. an admissible observation-to-stable-subject mapping.

The upstream provider qualification component is already production-refined by
`PHIL-PROV-QUAL-IMPL-001`. This slice therefore does not duplicate PROV-001–005.

## Extracted decisions

`ProviderEvidenceQualificationImplementation.v` owns four executable decisions
over reflected facts:

- `decideProviderEvidenceCompetenceByFacts` preserves the production/Certified
  rejection order for qualified-operation membership, operation, family,
  parameters, stable subject, and validity;
- `decideDirectEvidenceSubjectMappingByFacts` accepts only an exact stable
  observation whose mapped subject is the proposition subject;
- `decideCheckedEvidenceSubjectMappingByFacts` requires exact observation first
  and exact stable subject second; and
- `decideRuntimeCoincidenceSubjectMapping` always rejects.

The Rocq correspondence proves sound/complete mapping decisions against the
Certified `EvidenceSubjectMappingAdmissible` relation under explicit Boolean
reflection hypotheses. The prefix decision is characterized by the conjunction
of all reflected facts.

## Native bridge boundary

Production remains responsible for reflecting these concrete facts:

- membership of the required operation in the already-checked provider
  qualification;
- equality of `ProviderOperationKey`, proposition-family keys, `[RefTerm]`
  semantic parameters, stable-subject keys, and validity-contract keys;
- equality of concrete `ProviderEvidenceObservation` values; and
- the concrete correspondence between Haskell `Text`, `LoanScopeKey`,
  `RefTerm`/`Proposition`, and the normalized Certified atoms.

No claim is made here about proposition truth, cryptographic correctness,
external observation-mapping truth, generic consume/reconstruct evidence
transport, provider lineage/admission, Systems preservation, target realization,
or final source syntax.

## Staging verification

The existing registered `Phase 1 Provider Evidence Proofs` workflow is extended
additively to:

1. recompile the Certified provider-evidence proof;
2. compile the implementation correspondence and fresh extraction;
3. strict-typecheck the extracted kernel;
4. run fourteen direct extracted-kernel controls covering acceptance and every
   ordered rejection;
5. strict-typecheck unchanged production;
6. rerun unchanged provider qualification, PROV-010, and Steve provider
   correspondence corpora; and
7. record exact staging SHA-256 identities.

A green staging run is mechanized evidence only. Production
`checkProviderEvidenceProducerCompetence` remains unchanged until a subsequent
closeout PR checks in the exact harvested kernel and routes the existing semantic
decisions through it.
