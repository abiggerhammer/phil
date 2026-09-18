# PHIL-P1-REPLACE-001 proof boundary

This slice certifies the Phase-1 provider-replacement integration witness.

It does not define a new replacement relation.  It composes the already
Certified / implementation-refined provider-replacement qualification and
architecture-realization authorities around the exact ARCH-010 integration
witness.

## Certified aggregate

A valid integrated provider replacement has:

- two independently admitted provider sides;
- one unchanged public provider interface;
- one unchanged provider occurrence;
- one unchanged ArchitectureInstance identity;
- a distinct replacement provider subject;
- a distinct ArchitectureRealization revision;
- fresh qualification claim, evidence, and admission lineage for the
  replacement side;
- explicit scoped reuse for every evidence reference shared across both claims;
- an exact ArchitectureRealization bridge for both the predecessor and
  replacement sides.

Consequently:

- predecessor evidence cannot qualify the replacement claim by inheritance;
- changing abstract architecture topology is not provider replacement;
- unchanged selected-realization identity is not provider replacement;
- shared evidence without an exact reuse record and validity scope rejects; and
- rebuilding the same exact instance with the same selected realization is
  deterministic.

## Certified predecessors

The proof composes:

- `PHIL-PROV-REPLACE-001` / PROV-015 for independent admission, fixed
  interface/occurrence/instance, fresh replacement lineage, and scoped shared
  evidence; and
- `PHIL-ARCH-REALIZE-001` / ARCH-010 for exact ArchitectureInstance binding,
  changed ArchitectureRealization identity, and topology-change rejection.

## Production correspondence

The unchanged ARCH-010 integration corpus is
`test/Phase1ArchitectureProviderReplacementMain.hs`.  It constructs two
different provider DefinitionRevisions over one stable Steve store
ArchitectureInstance, derives independent claim/evidence/admission identities,
constructs both ArchitectureRealizations, and checks:

- stable interface and ArchitectureInstance;
- changed realization;
- accepted replacement pair;
- scoped shared evidence / assumption reuse;
- exact derived revisions;
- fresh lineage;
- deterministic rebuild;
- predecessor-evidence rejection; and
- topology-change rejection.

## Explicit boundaries / TCB

Still explicit:

- concrete canonical SemanticForm and digest/revision construction;
- Text/Map/Set representation and finite enumeration;
- truth and completeness of provider qualification evidence;
- external provider behavior and deployment/runtime assumptions;
- GHC/runtime correctness;
- Rocq/toolchain correctness; and
- target/backend correctness beyond the already-certified realization boundary.

This aggregate certifies composition of the two independently justified
provider realizations.  It does not claim that one implementation's evidence
proves another implementation correct.
