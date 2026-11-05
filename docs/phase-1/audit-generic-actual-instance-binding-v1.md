# D-ARTIFACT-MANIFEST-REFLECTION-01 — exact generic actual/instance correspondence

**Date:** 2026-11-05. **Predecessors:** [#1577](https://github.com/abiggerhammer/phil/pull/1577) native final authority adapter and [#1579](https://github.com/abiggerhammer/phil/pull/1579) checked declaration-level source/manifest producer. This is a bounded implementation correspondence refinement.

## Gap being closed

The #1579 producer verified that the accepted generic application's declaration key, interface revision, and definition revision appeared in the source verification bundle. It did **not** establish which architecture instance that application corresponded to, nor whether its complete generic static arguments were identical to the instance's static bindings.

## New checked path

`closeSourceManifestBindingForInstance` receives an accepted `GenericApplicationAssurance`, an explicit `ArchitectureInstanceDescriptor`, the verification bundle, and the same policy/context/ledger/selection already accepted by `closeVerificationBundle`.

Before constructing the opaque source/manifest association, it:

1. Requires the descriptor's exact declaration, interface, and definition lineage to equal the accepted application's declaration lineage.
2. Compares all generic static arguments with all of `architectureStaticBindings` by exact map equality, converting only the generic argument key wrapper to its existing `Text` name. Neither a missing nor extra static binding can be ignored.
3. Recomputes `deriveArchitectureInstanceIdentity` from the complete descriptor, including instance key, parent key, declaration lineage and static bindings, and requires that recomputed canonical identity in the accepted `VerificationBundle` instance set.
4. Reuses the existing #1579 declaration membership and ordinary `closeVerificationBundle` producer path to close the manifest. The returned constructor is private; `bindProducedFinalAuthority` still requires exact equality with the independently accepted release manifest and complete StageClosure.

The existing weaker `closeSourceManifestBinding` remains available as a declaration-only interface; it is not silently promoted to an instance-backed guarantee. Callers seeking actual/instance correspondence must use the stronger function.

## Adversarial controls

The Upload and Steve producer-positive fixture now uses an accepted generic application with the nonempty semantic argument `T = Blob`, an exact architecture descriptor, and its recomputed canonical instance identity in the verification bundle.

Negative controls reject a changed `T` value, missing `T` binding, an unregistered instance key/revision, and a descriptor with a substituted definition revision. The earlier producer and INT-005 manifest/stage/LLVM/trust controls remain unchanged. A dedicated GitHub Actions workflow enforces the complete strict Haskell build, exact typecheck and all tests under GHC 9.6.7.

## Limits

This is a **bounded native correspondence check** between an accepted generic application and a registered canonical architecture instance descriptor. A caller still supplies the descriptor and the VerificationBundle; acceptance of their source production and completeness is an inherited predecessor. This does not prove arbitrary whole-program architecture graph membership beyond the selected instance, native-to-Rocq `nat` representation or the final semantic proof adapter, external provider/assumption authority, public release asset bytes, or final independent audit signoff.

No generic semantics or canonical instance identity derivation algorithm was rewritten. Do not claim Phase 1 independent-audit freeze from this tranche. Historic findings and the original 244 conformance cases are unchanged.
