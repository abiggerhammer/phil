# P8-A — accepted-domain representation census and counterexample ledger

**Baseline:** main merge `4fd2c981a599008bec5d202362f0210a8043e655`,
2026-11-14, following protected P8/P9 lane bootstrap #1773.
**Controlling issue:** [P8 #1770](https://github.com/abiggerhammer/phil/issues/1770);
umbrella [#1584](https://github.com/abiggerhammer/phil/issues/1584);
dependent [P10 #1772](https://github.com/abiggerhammer/phil/issues/1772)
is **BLOCKED on P8 and P9**. This document inventories, does not discharge,
the whole accepted-domain Haskell ↔ Rocq representation obligation.
See [2026-11-10 audit closeout](../../audit/phase1-impl-audit-1584-closeout-inventory-2026-11-10.md)
and [native correspondence proof boundary](audit-native-final-instance-typed-correspondence-v1.md).

## 1. Exact native structures, domains and owners

| Coordinates | Actual native type/owner and selected path | Existing bounded evidence | Missing P8 representation proof |
|---|---|---|---|
| Source D/V/Q/M | `Phil.Core.Generic.GenericApplicationIdentity`: `DeclarationKey` D; `InterfaceRevision` V; `Map GenericStaticParameterKey SemanticForm` (Q/M). Actual producer `deriveGenericApplicationIdentity`, then generic assurance lineage and `closeSourceManifestBindingForInstance` | Exact native input key-domain uniqueness before insertion; Map ordered/unique; atom-only D/V/Q/M optional wires | Full recursive `SemanticForm` model, total native Text transport, key/value equality, full map normalization and reflection into actual checked source |
| Recursive M | `Phil.Core.Static.SemanticForm` has `SemanticAtom Text`, `SemanticOrdered [SemanticForm]`, `SemanticUnordered (Set SemanticForm)`, `SemanticRecord (Map Text SemanticForm)`, deriving native `Eq, Ord` | `canonicalSemanticForm` recurses, using `Set.toAscList`, `Map.toAscList`, and length-prefixed raw `Text` atoms/field names; atom-only optional wires reject nested values | Define/check equivalent Rocq recursive representation and faithful `Text`, list/Set/Map semantics, complete accepted input codec; no accepted-domain restriction to atom leaves |
| Checked K/I | `ArchitectureInstanceDescriptor` (`InstanceKey`, optional parent K, full `DeclarationIdentity`, `Map Text SemanticForm` bindings) → `deriveArchitectureInstanceIdentity` and required membership in `VerificationBundle` | Private checked source-manifest binding retains descriptor; typed K and I data roles | Preserve checked occurrence K/I and independent production lineage; same I but different K must remain distinct; full descriptor fields must map |
| Selected source | `GenericApplicationAssurance` and `CertifiedSourceManifestBinding` (private checked token), `CertifiedApplicationArtifact` | Exact whole-object retained by `NativeFinalInstanceCorrespondence`; Upload/Steve accepted replay in `test/Phase1INT005CertifiedReleaseEnvelopeMain.hs` | Corresponding actual accepted Rocq source proof, not a supplied model `Prop` |
| Manifest | `Phil.Assurance.Types.AssuranceManifest`: 3 base digests, target/profile Text, obligation/certification/evidence/assumption/export/use Sets, lowering root Digest, validity `Map Text Text`; `manifestId :: Digest` | `closeVerificationBundle`, `verifyManifest`, private binder checks whole selected manifest | Full identity and content mapping of each field, including sets/maps and opaque referenced evidence; P9 owns competence of inherited acceptance |
| R/L | `manifestImplementationDigest :: Digest` raw Systems R; `manifestLoweringLedgerRoot :: Digest` L. `NativeRawSystemsDigest`/`NativeLoweringRootDigest` roles in `NativeFinalInstanceCorrespondence` | Role-tagged partial diagnostic Text and native equality with actual Systems digest and lowering ledger | Independent total injective `Digest` + text/byte representation into Rocq, no exchange of R with L, no unsupported high-bit exclusion |
| S/C/F | `StageClosureBundle` retains normalized `SystemsArtifactRevision` S, common `Phase1StageContractRevision` C, closed `ClosedStageContractRevision` F | Selected stage getters and distinct role tags, exact whole source/release StageClosure equality | Whole-stage representation and proof that accepted producer emitted it, not three unrelated revision string equalities |
| B/I_stage/A/P | `SubjectStageRevision` B; concrete StageClosure `InstanceRevision` I; `RealizationRevision` A; verifier-profile plain `Text` P | Type-separated B/I/A/P diagnostic wires; I checked via equality gate but no accepted occurrence K appears on StageClosure | Whole object and Unicode P transport, preserving independent concrete I from checked occurrence; occurrence→stage provenance remains open |
| Whole release | `CertifiedReleaseArtifact`: release profile (target, manifest compilation profile, LLVM profile and required trust kinds), whole `AssuranceManifest`, `StageClosureBundle`, `LLVMArtifact`, `Map ReleaseTrustBoundaryId ReleaseTrustBoundary` | `certifyReleaseArtifact` independently checks LLVM and residual trust; private final witness retains whole source/stage/release | Full Haskell→Rocq release object reflection and source→shipped bytes; actual LLVM/compiler/runtime/target remains declared Phase 1 TCB, not proved |
| Rocq model | `proof/Phil/Verification/NativeFinalInstanceTypedCorrespondence.v` abstract `Type` fields, typed equality and `represent*` functions supplied as parameters | Conditional transport, injectivity *premises* and negative noninjectivity results; named `Print Assumptions` exercised by existing workflow | Concrete native encoders for every accepted type, a verified bijective/reflection link to model inhabitants from checked native production; no role wires promoted to accepting facts |

The selected whole-object path is
`closeSourceManifestBindingForInstance` →
`closeVerificationBundle` → `bindProducedFinalAuthority` →
`bindNativeFinalAuthority` →
`closeNativeFinalInstanceCorrespondence`.
It requires independent source/release acceptance and exact selected
`StageClosureBundle` equality. The existing P2/P6/P7 seal is useful input;
it is NOT itself the missing P8 interpretation or origin proof.

## 2. Concrete domain mismatches (executable negative discrimination)

`test/P8AcceptedDomainBoundaryMain.hs` runs the **real native exported
functions**, not a second invented model. The tests demonstrate:

1. `Text` values U+00E9, U+1F642, embedded U+0000 and distinct composed vs
   decomposed forms. `Text.length` is not UTF-8 byte length.
   `canonicalSemanticForm` embeds the native raw Text after a character count;
   its existing framing is *not* a checked Rocq String parser.
2. `deriveGenericApplicationIdentity` with an actual recursive
   `SemanticRecord` holding `SemanticOrdered` and nested
   `SemanticUnordered` succeeds, retaining complete Q/M actuals. This
   **only** establishes permissive native identity derivation; it is not a
   `GenericApplicationAssurance` or final accepted release.
3. `encodeNativeGenericAtomApplicationWires`,
   `encodeNativeSemanticOrderedAtomWires`,
   `encodeNativeSemanticUnorderedAtomWires` and
   `encodeNativeSemanticRecordAtomFieldWires` fail closed with `Nothing`
   on structured children. The runtime's optional atom-only diagnostics are
   therefore STRICTLY WEAKER than the structurally legal identity domain.
4. Real native Map/Set sorting and duplicate behavior are distinguished:
   `deriveGenericApplicationIdentity` rejects a duplicate Q key *before*
   `Map.fromList` could overwrite it; `Set.fromList` deduplicates;
   partial wire decoders reject repeated/out-of-order keys. Neither a Haskell
   Map's `toAscList` nor a Rocq list alone proves cross-language ordering.
5. Q vs M and R vs L roles reject substitution even when their textual
   payload is identical. This says nothing about independent digest
   computation or authentic origin.
6. The real accepted Upload/Steve producer→manifest→whole StageClosure/
   certified release replay is rerun in the dedicated workflow, **separately**
   from the data-only negative probes; no recursive application is
   misreported as independently source+release accepted.

The optional ASCII-7 R/L/P diagnostic stages in
`NativeFinalInstanceCorrespondence` reject high-bit candidates. They have
**not** changed `Digest` or verifier-profile native acceptance; they are not
sound grounds for silently changing the accepted domain. Unicode, validity,
ill-formed byte encodings, normalization, exact UTF-8/code point model and
canonical/duplicate key collision must be specified in a future competent
full-domain codec, not reconstructed from a caller-controlled Text token.
Haskell `Text` values are well-formed text values, whereas arbitrary
byte input needs an independently specified decode/rejection policy.

## 3. Finite next work and real stop criteria

**This PR1 is an executable census and non-closure witness.** Its checks are
strict native `-Wall -Werror` data probes, plus original Upload/Steve whole
acceptance replay and existing conditional Rocq assumption queries under
Rocq 9.2.0. The tests do NOT purport to prove the correspondence theorem.

**Candidate PR2 (only after this exact PR is merged):** one P8-owned
constructor-complete *data-level* `SemanticForm` representation with a
precisely specified Unicode/text and finite Map/Set ordering model,
round-trip/injection/negative controls, and a proof about exactly those
claims. It must identify whether the true accepted Haskell domain can be
represented without introducing new Text/UTF-8 premises in the TCB and
whether that object connects to the checked producer, not just standalone
values. If it cannot, stop with a minimal counterexample and request an
explicit maintainer semantic/TCB decision. Do not use invented `nat`
identifiers or upgrade any abstract `represent*` parameter to authority.

P8 remains **OPEN and not discharged**. P9 governs checker/evidence,
assumption and erasure competence, and P10 has no authority to derive
`FixedFinalAuthorityAdapter` or `FinalArtifactCertified`.
No change to original 244 normative cases, existing accepted semantics,
`proof/Phil/Surface`, FSEM, signed/public release bytes, LLVM TCB,
proof axioms or Phase 1 freeze status.
