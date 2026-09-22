# PHIL-AUD-PREREQUISITE-SUPPORT-001 proof boundary

This slice records the producer-side assurance relation discovered while
following certificate assumptions into manifest closure.

## Native relation

`Phil.Core.Discharge.resolveObligation` recursively resolves focused side
conditions as child obligations. When a child is established locally, the
parent decision procedure receives a
`SolverAssumption (PrerequisiteFact childId) ...`. A
`StaticByCertificate` parent may therefore be valid only because that child
prerequisite was available.

`Phil.Assurance.Handoff.handoffResolvedObligation` currently preserves the
tree as revision-generation provenance: the child revision records the parent
in `revisionGeneratedFrom`.

Those relations have different directions and different meanings:

- semantic prerequisite/support: **parent depends on child**;
- generation provenance: **child generated from parent**.

`VerificationObligationGraph` defines an edge `(A,B)` to mean A depends on
B. Consequently a direct projection of `revisionGeneratedFrom` yields the
opposite edge for a generated prerequisite and cannot by itself establish the
support used by a parent certificate.

## Proof surface

`proof/Phil/Assurance/PrerequisiteSupport.v` models:

- resolved parent-to-child prerequisite relations;
- child-to-parent generation provenance;
- the exact prerequisite relation used by a certificate; and
- the obligation-dependency relation retained by the resulting evidence.

The proof establishes that every prerequisite used by a certificate requires
an explicit evidence dependency in the same parent-to-child direction.
A concrete two-revision witness demonstrates that lineage-only projection
preserves provenance while failing certificate-support preservation. A
companion witness shows that explicit support can coexist with unchanged
generation provenance.

This extends, rather than replaces, `PHIL-ASSURE-LINEAGE-001`: lineage is
still provenance, and explicit `DependsOnObligation` remains the authority
relation consumed by manifest verification.

## Remaining implementation correspondence

This PR does not change production Haskell. The next remediation slice must
bind the actual `ResolvedObligation` prerequisite tree and any
`DecisionCertificate` prerequisite use to explicit support carried into the
assurance graph/evidence records, without reversing or repurposing
`revisionGeneratedFrom`.

Concrete ObligationId-to-RevisionId mapping, certificate traversal, Haskell
Map/Set enumeration, EvidenceEntry construction, and the final INT-002
consumer remain implementation-correspondence boundaries.
