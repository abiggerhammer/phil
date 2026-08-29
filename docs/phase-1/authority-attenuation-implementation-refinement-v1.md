# Authority attenuation implementation refinement v1

`PHIL-AUTH-ATTEN-IMPL-001` mechanically connects production AUTH-003 attenuation, semantic-boundary, and authority-join acceptance to the already-Certified `PHIL-AUTH-ATTEN-001` semantics.

## Executable semantic seam

The extracted kernel owns three final semantic decisions over representation-neutral Boolean facts:

1. **Explicit attenuation** — exact subject preservation, no authority widening, and exact witness binding to source contract, target contract, subject, and complete visible operation set.
2. **Semantic boundary visibility** — exact subject preservation and non-widening, plus either an unchanged contract with exactly unchanged visible operations or an explicit valid attenuation witness for a changed contract.
3. **Authority join** — at least one continuing branch, exact subject and contract agreement on every continuing branch, and joined operations available on every continuing branch rather than unioned from branch-local authority.

Each acceptance theorem is sound and complete for the corresponding Certified proposition under explicit reflection hypotheses connecting native Boolean facts to the representation-neutral semantic relation. Coq `bool` is extracted directly as `Prelude.Bool`, so production can pass the native facts to the kernel without a handwritten Boolean representation bridge.

## Production binding

`src/Phil/Core/AuthorityAttenuation.hs` now computes the concrete representation facts and routes every successful explicit attenuation, boundary transition, and authority join through the checked-in `AuthorityAttenuationKernel` decision. Existing diagnostic distinctions remain native explanations of a kernel rejection. If a kernel result disagrees with the concrete facts used to construct its inputs, production fails closed with `AuthorityAttenuationKernelBridgeMismatch`.

In particular:

- explicit attenuation success requires the extracted conjunction to accept all six exact native facts;
- unchanged-contract boundaries require both exact contract and operation-surface equality;
- changed-contract boundaries require a present witness whose exact attenuation facts are accepted;
- joins require a nonempty branch list, matching subjects and contracts, and joined operations contained in the intersection of every continuing branch; and
- an empty join is explicitly rejected through the extracted nonemptiness gate.

## Explicit representation boundary

Production continues to own the concrete finite facts:

- `AuthorityContractKey`, `AuthoritySubjectKey`, and `AuthorityOperationKey` equality;
- `Data.Set` equality, difference/subset facts, intersection, membership, and canonicalization;
- finite branch-list traversal and nonemptiness;
- `Maybe AuthorityAttenuationWitness` representation; and
- exact diagnostic payload/order and accepted value reconstruction.

Those native facts must reflect the Certified predicates exactly. Handwritten bridge and diagnostic code may reject on disagreement but may not turn an extracted-kernel rejection into success.

## Validation

The dedicated workflow recompiles the Certified authority proof chain and executable correspondence under Rocq 9.2.0, fresh-extracts `AuthorityAttenuationKernel.hs`, requires byte identity with the checked-in kernel, and typechecks both the exact generated kernel and bound production under GHC 9.6.7 with `-Wall -Werror`.

It reruns the bound authority-possession dependency corpus, the existing 19-case AUTH-003 attenuation corpus, and a direct production-binding corpus covering empty-join rejection, exact attenuation acceptance, missing-witness rejection for contract changes, and witnessed boundary narrowing. It records hashes for the exact kernel, production binding, and both attenuation corpora as closeout evidence.

On an all-green exact head, `PHIL-AUTH-ATTEN-IMPL-001` is ready to move from `Active / Mechanized` to `Discharged / Implementation Refined`.
