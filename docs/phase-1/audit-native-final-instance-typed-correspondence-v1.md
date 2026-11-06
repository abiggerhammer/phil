# D-ARTIFACT-MANIFEST-REFLECTION-01 — typed native final-instance intermediate

2026-11-05. Controlling handoff: #1584. Predecessors: merged #1575, #1577, #1579 and #1583. This is a **bounded positive/negative native-to-model boundary**, not complete final-artifact certification.

## Executable native producer/consumer chain

`Phil.Verification.NativeFinalInstanceCorrespondence.closeNativeFinalInstanceCorrespondence` takes an accepted `GenericApplicationAssurance`, a concrete `ArchitectureInstanceDescriptor`, an actual `VerificationBundle` with policy/context/ledger/selection, and **independently accepted** `CertifiedApplicationArtifact` and `CertifiedReleaseArtifact`. It invokes the exact #1583 `closeSourceManifestBindingForInstance` producer (same declaration/definition/interface, exact static-argument map, canonical instance identity present in that bundle, and checked INT-002 manifest closure). It then uses #1579's `bindProducedFinalAuthority` and #1577's `bindNativeFinalAuthority`: same produced manifest as release manifest, accepted source identity, **complete StageClosure object**, independently checked raw Systems artifact digest and lowering ledger root.

The returned constructor is private. Its two projections retain *separately* the checked `ArchitectureInstanceIdentity` and the pre-existing `NativeFinalAuthority`. The latter retains accepted `GenericApplicationIdentity`, manifest `Digest`, raw Systems `Digest`, lowering root `Digest`, subject `SubjectStageRevision`, stage `InstanceRevision`, `RealizationRevision`, normalized `SystemsArtifactRevision`, common `Phase1StageContractRevision`, final `ClosedStageContractRevision`, and verifier-profile `Text`. No conversion between these distinct revision/digest domains is inferred.

The strict Haskell replay must accept both Upload and Steve and reject altered semantic actuals, substituted declaration, unregistered architecture instance, swapped certified release manifest, and source/release StageClosure disagreement. The existing INT-005 suite retains raw digest, root, LLVM, trust and final-stage negative controls.

## Rocq boundary and assumptions

`NativeFinalInstanceTypedCorrespondence.v` quantifies over **distinct abstract native types**, without pretending that `Digest`, canonical instance identity, or revision strings already have a proved encoding into the semantic model's `nat` fields. Its producer/consumer relation preserves exact source application, manifest, StageClosure, raw digest and lowering-root equality and supplies negative theorems for each mismatch. The architecture occurrence-to-concrete-stage instance relation is a **separate explicit premise**; negative pressure shows it cannot be omitted.

The proof deliberately does **not** construct `FixedFinalAuthorityAdapter`, `FinalManifestRepresentsRelease`, `SourceAssuranceValid`, `ArtifactStagePreserved` or `FinalArtifactCertified` from native input. Rocq `Print Assumptions` is run on both the new boundary and the existing conditional fixed-adapter theorem.

## Still-open competence/premise ledger

1. Authenticate that accepted generic semantic application and declaration-level manifest selection cover the *entire* source application and that the actual architecture occurrence corresponds to the *concrete stage* instance revision; merely sharing a name or revision is insufficient.
2. Supply and prove an injective, domain-respecting Haskell-to-Rocq representation for each necessary field (application, manifest, raw digest/root, normalized Systems, common/closed contracts, subject/instance/realization/profile), and a reflection theorem from the accepted opaque native objects to the model facts. No ad hoc `nat` identifiers.
3. Reconcile source/assumption/erasure and StageClosure proof predecessors to the exact accepted native release without taking a caller-supplied model `Prop` as producer authority.
4. Revalidate public release **bytes** and independent pinned final-delta signoff separately; LLVM and provider/runtime trust remain Phase-1 TCB.

The independent audit freeze verdict remains **NOT YET**. No change to 244 normative cases, historical audit evidence, release artifacts, or Phase 2 features. Passing this slice is evidence only of the bounded checked chain and typed negative model pressure.

## 2026-11-06 — necessary stage-instance revision gate (issue #1584)

The sealed native witness now has a distinct opt-in
`checkNativeStageRevisionEquality` gate. It compares
`identityInstanceRevision (deriveArchitectureInstanceIdentity descriptor)`
to `nativeFinalInstanceRevision` read from the **already accepted**
`NativeFinalAuthority`/concrete StageClosure. Its success record's constructor
is private. Mismatch includes the expected canonical and actual accepted
`InstanceRevision` values; this cannot be bypassed by substituting the
manifest, Systems revision, common stage contract or closed revision.

The independent NR-D06 source occurrence is not the occurrence that produced
the Upload or Steve stage fixtures. Both *still* close the original bounded
manifest/source/StageClosure witness; both **must fail** the stronger necessary
revision gate, rather than being presented as full source-to-stage provenance.
A separate Haskell negative shows two distinct occurrence keys with equal
`InstanceRevision`. The Rocq extension proves drift blocks the necessary
equality gate, makes the missing occurrence-to-stage origin relation explicitly
independent, and gives a concrete *logical counterexample*, not a native
`nat` encoding. The CI replay includes `Print Assumptions` for those theorems.

**What this does not establish:** equality of revisions is not enough to
authenticate the occurrence key and its stage-production lineage. Even an
eventual passing gate cannot discharge `architectureOccurrenceRepresentsStageInstance`,
the fixed-adapter representation, source/assumption/erasure predecessors,
`FinalArtifactCertified`, public-release byte verification, or independent
final-delta approval. These remain separate obligations; Phase 1 audit freeze
is **NOT YET**, and 244 normative cases are unchanged.

## 2026-11-06 — conditional, domain-separated model transport (issue #1584)

The next bounded proof slice formalizes what an eventual representation layer
would *have to* establish before it could support native-to-Rocq final
authority. The actual checked native producer/consumer equalities transport
forward through five separately typed **parameter** functions: application
identity, manifest identity, whole StageClosure, raw Systems digest, and
lowering ledger root. In particular, although native Haskell uses the same
Digest type for raw Systems and ledger roots, their **model target types and
representation functions are distinct**. This is not a map from those values
to the model's existing nat fields.

The reverse theorem requires **five separate injectivity premises**; its
conclusion is limited to those five native equality propositions, never the
independent acceptance or origin of their inputs. A concrete proof-level
counterexample uses an explicitly noninjective bool-to-unit mapping to
demonstrate how distinct native-side values could collapse to one modeled
value. That example is **not** a purported native Digest encoding. Rocq
Print Assumptions replays both directions and the counterexample, and the
unchanged but reexecuted strict Haskell Upload/Steve and adversarial
producer/consumer suite remains the executable native control.

**Still missing:** actual total and injective representations (and their
faithfulness proofs) for every required source, manifest and stage coordinate;
the occurrence-key/stage-production origin, all normalized Systems, common
and closed contract, subject/instance/realization/verifier-profile model
translations, predecessor source/assumption/erasure authority, and a
competent producer that ties the representations to accepted native
objects. None is supplied by this parametric transport. Release public bytes
and independent pinned final-delta signoff remain separate; audit freeze
**NOT YET**. This does not modify the 244 normative conformance cases.
