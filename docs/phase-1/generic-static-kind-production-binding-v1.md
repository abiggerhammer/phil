# Generic Static Kind production binding v1

`PHIL-GEN-KIND-001` is production-bound to the exact Rocq-extracted kernel staged in #619.

## Exact staged lineage

- staging PR: #619
- repaired exact green staging head: `31501bc6355b49dc282f670cd573053b4f283611`
- staging merge: `33be843fb9462e37cbdc658be951f6397e0eac3f`
- dedicated run: `33736125280`
- staging artifact: `9885871378`
- artifact digest: `sha256:0e92bdd2f06311ba30edfbb9087ba4be968fc08baa99a578c2cea637fc2ce9ef`
- exact `GenericStaticKindKernel.hs` SHA-256: `11b37e69f97ab68e7e3615faed701251759a850dda1b6d207dc61312478ccce0`
- exact kernel Git blob: `0434c5a46e1953c4b394248d23c9b851de807332`

Both `generated/GenericStaticKindKernel.hs` and `src/GenericStaticKindKernel.hs` are the exact staged bytes.

## Production ownership split

`Phil.Core.Generic.StaticActual` keeps the concrete finite representation and orchestration:

- duplicate generic-static-parameter detection and its diagnostic;
- parameter/actual telescope arity checking;
- concrete `Text`, `GenericStaticParameterKey`, `GenericStaticKind`, and `SemanticForm` equality;
- candidate construction, name filtering, expected-kind filtering, and candidate ordering;
- available-kind and ambiguous-semantic-form diagnostic payload construction; and
- checked-result construction.

The exact extracted kernel owns the bounded semantic decision surface:

1. direct actual exact-kind admission;
2. referenced actual rejection precedence and admission from exact reflected facts; and
3. exact checked parameter-key/kind shape acceptance.

The bridge checks that every extracted constructor agrees with the native facts used to construct its inputs. Any impossible disagreement rejects with `GenericStaticKindKernelDisagreement`; handwritten bridge or diagnostic code cannot turn a kernel rejection into success.

For the current canonical candidate representation, a uniquely selected reference returns that candidate's `SemanticForm` directly, so `selectedSemanticFormExact` is true by concrete construction. The extracted semantic-form-mismatch decision remains a fail-closed guard against a future decoupled selector rather than a normal current diagnostic path.

## Closeout gate

The dedicated production-binding workflow:

1. recompiles Certified `GenericStaticKind.v` and `GenericStaticKindImplementation.v` under Rocq 9.2.0;
2. fresh-extracts `GenericStaticKindKernel.hs`;
3. requires SHA-256 `11b37e69f97ab68e7e3615faed701251759a850dda1b6d207dc61312478ccce0` and byte identity with both checked-in copies;
4. builds the broad library regression surface with warnings as errors;
5. strict-typechecks the exact kernel, bridge, bound production checker, direct extracted-kernel harness, production-binding harness, and unchanged GEN-013 corpus;
6. executes fourteen direct extracted-kernel controls;
7. executes nine production-binding controls; and
8. reruns the unchanged seven-case GEN-013 corpus.

On a fully green exact head, `PHIL-GEN-KIND-001` may be promoted to `Discharged / Implementation Refined` while parser-to-static-actual correspondence, candidate construction, concrete identity representations, and kind-specific semantic competence remain explicit boundaries.
