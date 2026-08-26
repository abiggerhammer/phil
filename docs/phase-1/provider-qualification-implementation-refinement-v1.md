# PROV-001–005 implementation refinement v1

`PHIL-PROV-QUAL-IMPL-001` is the mechanical production-correspondence migration for the already-certified stateless provider qualification core.

Provider qualification is the first migration with nested finite maps: public operations, explicit operation correspondences, implementation entries, implementation outcomes, and mapped public outcomes. Rather than re-encoding `Data.Map` semantics ad hoc inside the provider checker, this migration factors a reusable finite-association support kernel and builds the actual provider traversal on top of it.

The checked-in support kernel provides:

- exact pairwise key-domain comparison for canonical association lists;
- exact association-list lookup; and
- universal finite Boolean traversal.

Rocq proves key-domain comparison equivalent to equality of the finite key projections when the supplied concrete key equality is exact, proves lookup soundness and unique-key completeness, and proves finite Boolean traversal equivalent to `Forall`. CI now regenerates this support module and requires byte-identical equality with `src/ProviderQualificationKernelSupport.hs`.

The next extracted layer owns the nested provider decision itself. Its `decideProviderQualification` checks exact contract and implementation revisions, exact public-operation/correspondence key domains, explicit correspondence lookup for every public operation, exact implementation-entry lookup, a supplied per-operation semantic acceptance predicate, exact implementation-outcome/mapping key domains, mapped public-outcome lookup, and exact resource-residue equality. The per-operation predicate is the bounded composition point for the already `Implementation Refined` CALL-012 checker plus the no-stronger-preconditions check.

This head intentionally stages the new nested traversal before final production binding. CI compiles the new proof, extracts `ProviderQualificationKernel.hs`, typechecks it, and reruns the existing provider and CALL-012 behavior corpora. Once that extraction is green, the exact generated Haskell bytes will be checked into the same branch; production `checkProviderSemanticQualification` will then delegate acceptance to the extracted traversal with fail-closed `Map.toAscList` / `Map.fromList` bridges, and CI will require byte-identical regeneration of both provider kernels.

Only that final exact-head green closeout permits `PHIL-PROV-QUAL-IMPL-001` to become `Implementation Refined`.
