# PHIL-BND-SUBJECT-001 production binding v1

This closeout binds the production BND-012 byte-subject transfer gate and the
BND-013 zero-copy target gate to the exact Rocq-extracted decision kernel staged
in #475.

## Exact extracted kernel

`src/BoundarySubjectKernel.hs` is checked in byte-for-byte from the successful
#475 extraction:

`sha256:243656d82520d7909c9b1e39d799f4530c818ad20fff36319b7ecb496332d152`

The production-binding workflow fresh-extracts the kernel, checks that digest,
and byte-compares the fresh extraction with the checked-in production copy.

## BND-012: evidence subject transfer

`Phil.Systems.EvidenceSubjectTransfer` retains native stage construction,
`Map`/`Set` traversal, subject lookup, endpoint matching, source-evidence lookup,
and diagnostic payload construction.

The boundary-specific admission facts are reflected to
`decideBoundarySubjectTransferByFacts` in two places:

1. relation preflight supplies the copy/equality/transfer-law and validity-scope
   facts already available while checking a relation. The proposition-specific
   evidence gate is deliberately neutralized there because no concrete evidence
   reference exists yet;
2. each concrete evidence rebinding supplies all Certified facts, including
   exact membership of that evidence reference in the relation's allowed set.

Thus successful transfer of a concrete evidence reference must pass the exact
extracted Certified gate set. Runtime subject coincidence is also rejected by
the extracted decision. Native predecessor correspondence checks remain earlier
fail-closed guards rather than alternate transfer authority.

The Haskell `SubjectTransferBasis` representation has no checked non-copy
constructor, so the kernel's checked/non-copy failure constructor is unreachable
from the current production representation. It is nevertheless mapped
fail-closed.

## BND-013: zero-copy target realization

`Phil.Systems.BoundaryTargetRelation` first runs the existing target-strengthening
predecessor verifier. It then reflects the exact current Haskell facts to
`decideZeroCopyRealizationByFacts`:

- checked realization vs pointer reinterpretation;
- exact target-stage revision equality;
- boundary representation, grammar, and semantic value-type revisions;
- source semantic layout and concrete memory layout;
- endian/alignment/padding/tagging;
- lifetime and ownership/borrowing rules;
- device/storage-domain constraints;
- target assumptions/carriers.

Fact presence preserves the production rule exactly: `Text.strip` followed by a
nonempty check. The extracted decision owns the ordered final admission/failure
class, and Haskell reconstructs the pre-existing public diagnostics with the
same labels and stage-revision payloads.

## Explicit correspondence boundaries

This binding does not claim that native facts are true merely because they are
present. The following remain explicit realization/correspondence boundaries:

- truth of copy, byte-equality, evidence-transfer-law, layout, alignment,
  lifetime, ownership, device/storage, and target-assumption evidence;
- concrete `Text`, `Map`, `Set`, identifier, and stage-revision representation;
- the Certified DATA-SUBJECT predecessor and the native subject-correspondence
  and target-strengthening implementations;
- target-specific ABI/layout/aliasing facts;
- diagnostic payload construction;
- GHC/runtime and Rocq extraction/toolchain correctness.

A green exact-head production-binding workflow, byte-identical fresh extraction,
and unchanged 15-case BND-012/BND-013 corpus close the bounded implementation
correspondence for `PHIL-BND-SUBJECT-001`.
