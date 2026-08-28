# Authority attenuation implementation refinement v1

This staging tranche begins `PHIL-AUTH-ATTEN-IMPL-001`, mechanically connecting production AUTH-003 attenuation/boundary/join acceptance to the already-Certified `PHIL-AUTH-ATTEN-001` semantics without changing production behavior yet.

## Executable semantic seam

The extracted kernel owns three final semantic decisions over representation-neutral Boolean facts:

1. **Explicit attenuation** — exact subject preservation, no authority widening, and exact witness binding to source contract, target contract, subject, and complete visible operation set.
2. **Semantic boundary visibility** — exact subject preservation and non-widening, plus either an unchanged contract with exactly unchanged visible operations or an explicit valid attenuation witness for a changed contract.
3. **Authority join** — at least one continuing branch, exact subject and contract agreement on every continuing branch, and joined operations available on every continuing branch rather than unioned from branch-local authority.

Each acceptance theorem is sound and complete for the corresponding Certified proposition under explicit reflection hypotheses connecting native Boolean facts to the representation-neutral semantic relation.

## Explicit representation boundary

Production continues to own the concrete finite facts:

- `AuthorityContractKey`, `AuthoritySubjectKey`, and `AuthorityOperationKey` equality;
- `Data.Set` equality, subset/difference, intersection, membership, and canonicalization;
- finite branch-list traversal and nonemptiness;
- `Maybe AuthorityAttenuationWitness` representation; and
- exact diagnostic payload/order and accepted value reconstruction.

Those native facts must be reflected exactly. Handwritten bridge/diagnostic code may reject on disagreement but may not turn an extracted-kernel rejection into success.

## Validation

The dedicated workflow recompiles the Certified authority proof chain and new correspondence under Rocq 9.2.0, fresh-extracts `AuthorityAttenuationKernel.hs`, typechecks it under GHC 9.6.7, typechecks unchanged production `Phil.Core.AuthorityAttenuation`, and reruns the unchanged AUTH-003 corpus plus its authority-possession dependency corpus.

Production is unchanged in this staging tranche. On green, harvest the exact kernel/proof artifact, record `PHIL-AUTH-ATTEN-IMPL-001` as `Active / Mechanized`, merge, then production-bind final acceptance through the checked-in extracted kernel with fail-closed native Set/list/equality bridges.
