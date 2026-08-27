# Generic instantiation implementation refinement v1

This closes `PHIL-GEN-INST-IMPL-001` by binding the already Certified `PHIL-GEN-INST-001` semantics to production `Phil.Core.Generic` through two exact Rocq-extracted kernels.

## Exact disposition domain

`GenericInstantiationDomainKernel` owns the Boolean accept/reject decision for the requirement/disposition key domain. Production supplies only concrete `GenericRequirement` equality, the canonical ascending requirement keys, and the disposition-entry keys. Handwritten Haskell reconstructs the existing duplicate, first-missing, and first-unexpected diagnostics only after the extracted kernel rejects; disagreement with concrete `Map` normalization fails closed.

## Per-disposition validity

`GenericInstantiationValidityKernel` owns the semantic acceptance/error-class decision for each normalized disposition. Production supplies representation-neutral primitive facts derived from the concrete requirement, disposition, and policy:

- requirement kind;
- disposition kind;
- structural permission admission through the already refined generic structural kernel;
- exact provider-interface equality;
- checked provider-refinement target equality;
- exact proposition-evidence equality;
- assumption policy; and
- export policy.

The extracted kernel selects accepted, structural rejection, exact-provider mismatch, refinement-target mismatch, proposition-evidence mismatch, assumption forbidden, export forbidden, or kind mismatch. Handwritten Haskell reconstructs the existing concrete diagnostic payload. Any impossible kernel/concrete-shape disagreement fails closed.

## Trust boundary

The retained primitive foundations are Rocq extraction/toolchain correctness, GHC/runtime correctness, Haskell derived `Eq`/`Ord` consistency for the concrete identity types, exact `InterfaceRevision` and `Proposition` equality, `Map`/`Set` canonicalization, and the separately refined structural permission bridge. Checked-provider-refinement witness soundness remains the responsibility of the provider/ADR-021 layer; proposition truth and subject validity remain separate obligations.

## Closeout criterion

The dedicated workflow fresh-extracts both kernels and byte-compares them with the checked-in `src/` copies, typechecks the kernels and production bridge under `-Wall -Werror`, reruns the GEN-007/008/012 correspondence corpus, and records production-binding SHA-256 identities. Only a fully green exact head may upgrade the ledger row to `Discharged / Implementation Refined`.
