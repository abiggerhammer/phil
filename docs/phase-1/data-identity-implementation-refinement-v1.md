# Data identity implementation refinement v1

`PHIL-DATA-ID-001` is already Certified by `proof/Phil/Core/DataIdentity.v`. This tranche stages a representation-neutral executable decision seam without changing production.

## Extracted decision surface

`DataIdentityImplementation.v` extracts:

- `decideDataIdentityByFact`, which accepts exactly when the native fully-resolved nominal-identity equality fact is true;
- `decideDataOperationByFact`, which accepts exactly when the requested operation is explicitly present in the independent operation contract; and
- `decideDataOperationAfterIdentityByFacts`, which makes operation admission visibly independent of any identity fact.

Under explicit reflection hypotheses, the identity decision is sound and complete for Certified `DefinitionallyEqualDataType`, and the operation decision is sound and complete for Certified `permitsOperation`. The noninterference theorem proves that changing only the identity fact cannot change operation admission.

## Explicit native boundary

Production remains unchanged in this staging tranche. The following stay native representation/correspondence foundations:

- recursive traversal of concrete `TransparentAlias String DataTypeRef` values;
- concrete `String` nominal-key equality;
- source declaration-key and alias elaboration correspondence;
- `Data.Set` representation, insertion, membership, ordering, and canonicalization for operation contracts;
- the mapping between concrete `DataOperation` constructors and the Certified operation vocabulary; and
- diagnostic/result reconstruction.

The extracted kernel never infers operation authority from nominal identity, shape, alias presentation, or runtime representation.

## Staging validation

The dedicated data-identity proof workflow is extended additively to:

1. recompile the Certified `DataIdentity.v` theorem;
2. compile the executable correspondence and fresh extraction under Rocq 9.2.0;
3. strict-typecheck and execute direct controls against the fresh `DataIdentityKernel.hs`;
4. strict-typecheck the unchanged `Phil.Core.DataIdentity` and `Phil.Core.DataOperationContract` production paths; and
5. rerun the unchanged DATA-010/DATA-011 pressure corpora.

A green staging run records the exact extracted kernel identity while leaving `PHIL-DATA-ID-001` at `Discharged / Certified`. Production binding is a separate closeout tranche.
