# Phase 1 generic instantiation domain implementation refinement v1

Status: proof/extraction staging tranche for the exact-disposition-domain half of `PHIL-GEN-INST-IMPL-001`.

## Scope

`PHIL-GEN-INST-001` has two mechanically distinct acceptance layers:

1. the disposition domain must be exact — no duplicate requirement keys, every exposed requirement has a disposition, and no disposition exists for an unexposed requirement; and
2. every disposition in that exact domain must semantically satisfy its requirement under the enclosing policy.

This tranche refines only the first layer. Production `Phil.Core.Generic` is deliberately unchanged.

## Equality-parametric domain kernel

The certified proof model uses normalized `GenericRequirement` atoms, while production identities include concrete parameter keys, interface revisions, and propositions. Rather than inventing a serialization from those richer identities back into the proof atoms, the implementation proof factors exact-domain checking over an arbitrary key type and an equality predicate.

`exactKeyDomainb` checks three properties:

- disposition keys are duplicate-free;
- every required key occurs among the disposition keys; and
- every disposition key occurs among the required keys.

The generic theorem proves this Boolean checker equivalent to the corresponding `NoDup`/membership relation whenever the supplied equality test returns true exactly for equal keys.

A specialization with a proved `genericRequirementEqb` then establishes equivalence to the Certified `exactDispositionDomain` definition from `GenericInstantiation.v`. `decideExactKeyDomain` provides the extracted accept/reject decision.

This structure is intentional for the later production bridge: the checked-in extracted kernel can operate directly over production `GenericRequirement` values with the ordinary derived Haskell equality function. Concrete `Eq` correctness, `Set`/`Map` canonicalization, and GHC/runtime behavior remain explicit primitive representation foundations rather than being hidden behind a lossy proof-atom encoding.

## Production bridge boundary

The later production-binding tranche must:

1. check in the exact extracted `GenericInstantiationDomainKernel.hs` bytes;
2. require byte-identical fresh Rocq extraction;
3. feed the exact exposed requirement keys and submitted disposition keys to the extracted domain decision using concrete `GenericRequirement` equality;
4. preserve the existing fail-closed duplicate, missing, and unexpected requirement diagnostics;
5. ensure handwritten diagnostic reconstruction cannot turn an extracted domain rejection into acceptance; and
6. rerun the complete GEN-007/008/012 production correspondence corpus through the bound tree.

The second GEN-INST refinement seam — semantic validity of each individual disposition, including provider/interface equality, proposition evidence, structural mode satisfaction, and assumption/export policy — remains a separate executable-kernel tranche.

## Evidence level

A green staging tranche earns `Mechanized` evidence for the exact-domain sub-obligation only. It does not yet earn `Implementation Refined` for `PHIL-GEN-INST-IMPL-001` as a whole.
