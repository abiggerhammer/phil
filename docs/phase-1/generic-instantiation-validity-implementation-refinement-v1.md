# Generic instantiation validity implementation refinement v1

This tranche continues `PHIL-GEN-INST-IMPL-001` after the exact-disposition-domain extraction landed in #282.

It is a proof/extraction staging tranche only. Production `Phil.Core.Generic` remains unchanged.

## Scope

The Certified `PHIL-GEN-INST-001` model has two acceptance layers:

1. exact disposition-domain correspondence; and
2. semantic validity of each `(requirement, disposition)` pair.

#282 mechanized the first layer. This tranche mechanizes the second.

The executable validity kernel owns the eight-way decision:

- accepted;
- structural-mode rejection;
- exact-provider interface mismatch;
- checked-provider-refinement target mismatch;
- proposition-evidence mismatch;
- assumption not permitted;
- export not permitted; or
- requirement/disposition kind mismatch.

## Representation boundary

Production requirement identities are richer than the normalized Rocq model. The extracted kernel therefore consumes representation-neutral facts rather than forcing concrete Haskell identities through a synthetic `nat` encoding.

The eventual production bridge may compute only primitive facts:

- requirement kind;
- disposition kind;
- structural permission admission, itself supplied by the already refined structural kernel;
- exact provider-interface equality;
- checked-refinement target equality;
- proposition equality; and
- enclosing assumption/export policy bits.

The extracted kernel then exclusively owns acceptance and semantic error-class selection. Concrete `Eq` semantics for `InterfaceRevision` and `Proposition`, ordinary Haskell representation/runtime behavior, and the Rocq extraction toolchain remain explicit primitive foundations.

## Certified correspondence

`GenericInstantiationValidityImplementation.v` defines `validityFactsOf` over the Certified normalized model and proves:

- the extracted decision is accepted exactly when Certified `dispositionValid` is true;
- strict policy produces the explicit assumption-not-permitted decision;
- strict policy produces the explicit export-not-permitted decision; and
- provider binding presented for a proposition requirement yields the explicit kind-mismatch decision.

Provider-refinement soundness and proposition truth remain upstream assumptions exactly as in `PHIL-GEN-INST-001`; this tranche only decides the exact relation supplied to generic instantiation.

## What remains

A green exact-head run upgrades the semantic-validity half of `PHIL-GEN-INST-IMPL-001` to Mechanized. It does not yet make the umbrella Implementation Refined.

Final closeout still requires:

- checking both extracted kernels into `src/` byte-identically;
- routing production disposition-domain acceptance through the domain kernel;
- routing every per-disposition semantic acceptance/error-class decision through this validity kernel;
- fail-closed concrete bridges and exact existing diagnostic reconstruction; and
- the unchanged GEN-007/008/012 corpus passing through the bound production path.
