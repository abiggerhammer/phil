# D-CERT-SUPPORT-01 EvidenceFact authority proof boundary

This bounded proof-correspondence slice follows the checker-to-ledger support work landed through #1314, #1316 and #1321.

## What is already implemented

`Phil.Core.Discharge` derives local `EvidenceFact bindingName factIndex` assumptions from the canonicalized unrestricted Core evidence registry. `Phil.Assurance.Handoff.handoffResolvedObligationWithEvidence` then translates retained `EvidenceFact` references through an assurance-owned `(Name, Int) -> EvidenceEntryId` map and records them as `DependsOnEvidence`. The INT-002 handoff closure requires those immutable dependencies to be present on the selected certificate evidence entry.

That establishes lossless dependency transport once the map is authoritative. It does **not** by itself establish that an arbitrary supplied map identifies immutable evidence with the same semantic fact.

## Proof obligation

`proof/Phil/Assurance/EvidenceFactAuthority.v` models the remaining authority relation for a certificate-used local fact. For every used fact, preservation requires:

1. an authoritative local registry entry;
2. an immutable mapped evidence identity;
3. equality of the authoritative and immutable proposition identity;
4. equality of semantic-subject identity;
5. equality of scope identity; and
6. an emitted immutable evidence dependency.

The proof includes a negative witness in which the local map lookup succeeds and the dependency is emitted, but the immutable evidence has a different scope. That witness satisfies the weaker "mapped dependency only" property and fails full authority preservation. A positive witness preserves all three semantic components and the dependency.

The intended implementation correspondence is therefore stricter than map lookup:

`collectEvidenceAssumptions / resolveObligation`
→ exact certificate-used `EvidenceFact`
→ authoritative immutable evidence/revision identity with matching proposition, subjects and scope
→ `DependsOnEvidence`
→ existing INT-002 manifest closure.

## Boundary retained

This PR is proof-only. It does not claim that the current Haskell `(Name, Int) -> EvidenceEntryId` input already performs the authority check modeled here. The next implementation slice should bind that map to the same canonical evidence registry used by `resolveObligation`, validate the mapped immutable revision's semantic identity, and then reuse the existing handoff and manifest-consumer path rather than constructing a parallel support route.

The model does not grant truth to caller-supplied evidence, restore consumed linear resources for logical lookup, require whole-environment hashing, or alter direct-dependency reuse. LLVM and the other Phase 1 trusted-computing-base components remain unchanged and out of scope.

This slice is disjoint from the dedicated Surface Rocq refinement lane and the Core implementation-remediation lane active when it was opened.
