# P8-H7 — pure typed application inversion, not native or release authority

Date: 2026-11-16. Source checkpoint: `main 9d091797c69780e2571a0c29e9b71cbe6ab98d3c`.
Parent [P8 #1770](https://github.com/abiggerhammer/phil/issues/1770), [F2 STOP #1810](https://github.com/abiggerhammer/phil/issues/1810), [admission repairs H2/H4/H6 #1828](https://github.com/abiggerhammer/phil/issues/1828). This is a **new, disjoint pre-F2 pure-model proof** only; it does not allocate or activate the stopped original F2 slot.

## Concrete theorem target

The proof file `proof/Phil/Verification/P8H7ApplicationInverse.v` uses **the actual, unchanged E2 executable definitions** `p8_e2_put_application`, `p8_e2_parse_application_raw`, `p8_e2_parse_application_prefix`, `p8_e2_decode_application` and existing compiled F1 **recursive form prefix** theorem. No substitute parser, invented `nat` identity, supplied trust `Prop`, new axiom or changed older E1/E2/F1 proofs is permitted.

The new lemmas establish the typed D/V/Q/M app **prefix/remainder inverse** under `p8_d2_valid_application app = true`, using the exact E2 Q/M role tags, strict count, UTF-8 text framing, and F1's form fuel bound. Derived targets:

- `p8_h7_universal_model_application_inverse`: `decode (put app) = Some app` for every D2-valid application, not just E2's earlier `decode ... = Some app -> ...` soundness.
- `p8_h7_universal_model_application_injective`: equal emitted wires imply equal D2-valid typed applications.
- `p8_h7_universal_model_application_trailing_rejected`: a complete canonical app plus nonempty trailing bytes is not a complete accepted app.

The proof must compile under Rocq **9.2.0** with complete C1→D1→D2→E1→E2→F1→H7 imports, recursive `rocq check`, `Print Assumptions` on named theorems and no `Admitted`/Axiom/Parameter. Existing native GHC 9.6.7 `-Wall -Werror` diagnostic + actual Upload/Steve source tests are *regression controls*, not a proof that operational `Text`/`containers` obey the model.

## Accepted-domain boundary and explicit remaining gaps

Actual strong P2 `produceVerifiedSourceSystems` checks original native Core/context structures before source correspondence at [SourceSystems.hs](https://github.com/abiggerhammer/phil/blob/9d091797c69780e2571a0c29e9b71cbe6ab98d3c/src/Phil/Compiler/SourceSystems.hs); `validateNativeContainers` and `validateCoreNativeContainers` on [GenericLowering.hs](https://github.com/abiggerhammer/phil/blob/9d091797c69780e2571a0c29e9b71cbe6ab98d3c/src/Phil/Systems/GenericLowering.hs) cover recursive source/Core Map/Set inputs; checked static arguments [StaticActual.hs](https://github.com/abiggerhammer/phil/blob/9d091797c69780e2571a0c29e9b71cbe6ab98d3c/src/Phil/Core/Generic/StaticActual.hs) reject malformed selected recursive native semantic forms. These are executable **native gate observations**, not yet a Rocq reflection of `ActualAdmitted(x) ⇒ NativeInvariant(x)` for all public generic/assurance/release producers. In particular, public `deriveGenericApplicationIdentity` and `ArchitectureInstanceDescriptor` constructors are not themselves source-checked seals.

The *production* [canonicalSemanticForm](https://github.com/abiggerhammer/phil/blob/9d091797c69780e2571a0c29e9b71cbe6ab98d3c/src/Phil/Core/Static.hs) counts `Text` characters; the [P8SemanticFormCodec](https://github.com/abiggerhammer/phil/blob/9d091797c69780e2571a0c29e9b71cbe6ab98d3c/src/Phil/Verification/P8SemanticFormCodec.hs) is an explicitly **diagnostic UTF-8-byte-counted wire**. H7 does not identify these two framings or retroactively turn the diagnostic decoder into an accepted-release checker.

### Native→Rocq relations still required before F2/T6

- `R_T`: native, correctly represented `Text` to strict D1 octets with scalar and byte order and no hidden normalization; handle U+0000, U+00E9, decomposed e+U+0301, U+1F642, U+FFFD/surrogate-derived Text, capacity/error domains.
- `R_F`: recursive native `SemanticForm` with actual original, valid `Set`/`Map` shapes to D2 forms, mutual constructor/field/member order, duplicates and representation-soundness; distinguish native `Unordered < Record` from wire-byte order.
- `R_A`: native *accepted* `GenericApplicationIdentity` D/V/Q/M to D2 typed application, with full semantic actuals, checked source declaration, descriptor/assurance ancestry and no cross-role substitution.
- `R_{mathrm{release}}`: accepted opaque P2→P6→P7 exact K/I, raw Systems digest R, lowering L, Systems S, contracts C/F, subject B, stage instance I, realization A, verifier P, manifest, accepted release and LLVM/trust, rather than independently fabricated values or just a structural digest equality.

**Independent gates remain NOT ACTIVE:** [#1826](https://github.com/abiggerhammer/phil/issues/1826) requires a separately attested **exact selected toolchain/unit/ABI/linked-target identity** including `ghc-prim`, RTS and native C/C++ closure. [#1827](https://github.com/abiggerhammer/phil/issues/1827) requires independently reviewed and approved T1–T4 native semantic obligations on that exact build. The prior Astra technical review is **conditional adversarial input**, not human/independent TCB approval. Do not claim either gate closed or add an axiom.

P8-F2 stays **0/1 UNUSED/STOPPED**, the original P8-C3 **STOPPED**, P10 `FinalArtifactCertified` still unproved, Phase 1 freeze/audit #1584 still open. No grammar, source-language, TCB, release, P9/FSEM, historical proofs, 244 normative cases, or selected build changed by H7.
