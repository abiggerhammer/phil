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


## 2026-11-06 — seven-field typed StageClosure coordinate transport

Following merged #1590, the new bounded Rocq slice covers the *other seven*
concrete native StageClosure coordinates independently: subject, instance,
realization, **normalized** SystemsArtifactRevision, **common**
Phase1StageContractRevision, **final closed** ClosedStageContractRevision,
and verifier profile. Each source field and model codomain remains its own
type, deliberately separate from #1590's accepted source, manifest, whole
StageClosure, raw Systems digest, and lowering ledger root. These are
parameterized functions rather than unproved Haskell-to-Rocq nat encodings.

The positive theorem transports already-given equalities between two
independently typed native stage-coordinate records. The reverse theorem
requires **seven separately supplied injectivity premises** and recovers
only the seven equalities, not native authority. An explicit counterexample
uses distinct native/common and closed-stage logical types and distinct
model target types with noninjective maps to show why both model equalities
can hide two independent native drifts. This is not a model of actual
Haskell revisions or a claim that unrelated StageClosure objects can be
accepted. The exact-head workflow compiles the theorems and prints their
assumptions while reexecuting unchanged strict GHC/Haskell Upload/Steve
accepted-object and adversarial native/release tests.

**Still open:** implement and prove these seven real encodings and the five
earlier ones, authenticate the occurrence-key/stage-production origin,
reconcile full source/assumption/erasure and final predecessor authority,
and execute release public-byte and independent pinned final-delta
verification separately. No supplied model Prop creates native producer
authority; no full FixedFinalAuthorityAdapter or FinalArtifactCertified is
derived. LLVM/provider/runtime TCB and original 244 normative conformance
cases remain unchanged. Independent audit-freeze verdict: **NOT YET**.

## 2026-11-06 — exact accepted source-assurance object gate

The sealed native `closeNativeFinalInstanceCorrespondence` now fails closed
unless its generic source/manifest producer receives the **same complete**
`GenericApplicationAssurance` value as the independent
`CertifiedApplicationArtifact` source assurance. Merely comparing
`GenericApplicationIdentity` was insufficient: the same declaration and
semantic actuals may be paired with a *different* checked reusable-body
evidence artifact. The new error `NativeFinalInstanceSourceAssuranceMismatch`
does not disclose or fabricate proof contents. Both Upload and Steve positive
consumers continue to use exactly matching accepted assurance; both now have
a separate negative test built using the checked generic-assurance constructors
with **equal application identity but different source proof evidence**.

The matching Rocq boundary treats the full source assurance as a separate,
abstract type with an explicit identity projection. Its conditional theorem
preserves consumer identities only given an independently provided exact-source
gate; its mismatch theorem forbids substitution, and a logical noninjective
identity projection demonstrates why equality of identities alone cannot
authenticate the source object. No mapping from native evidence to Rocq is
invented. Exact-head Rocq `Print Assumptions` and strict native replay are
required before this addition earns any audit credit.

**Open:** a verified source-to-stage occurrence-key/production-lineage
provenance, actual faithful typed representation implementations and
injectivity, source/assumption/erasure and final predecessor proofs, release
public **bytes**, and independent pinned final-delta signoff. The complete
`FinalArtifactCertified` remains unproved, the 244 normative cases are
unchanged, and independent Phase 1 audit freeze remains **NOT YET**.

## 2026-11-06 — exact accepted source at the lower-level manifest/release binder

The exported `bindProducedFinalAuthority` was a separate entry point below
`closeNativeFinalInstanceCorrespondence`: its opaque
`CertifiedSourceManifestBinding` stored only `GenericApplicationIdentity`
alongside the checked closed manifest. Therefore, before this change, an
independently certified source artifact built from a *different* checked
`GenericApplicationAssurance` with the *same* semantic application identity
could pass the lower-level association, despite #1594's stronger high-level
source-assurance gate.

The opaque source-manifest producer token now retains the complete accepted
`GenericApplicationAssurance`. The lower-level binder compares it with the
independently accepted `CertifiedApplicationArtifact` source assurance and
returns `SourceManifestSourceAssuranceMismatch` before evaluating the released
manifest if they differ. Only after that check does it project the application
identity for the existing typed manifest/stage/digest/root consumer gate.
Upload and Steve replay the positive producer path and the distinct accepted
source-proof negative at this *lower-level* entry point. A Rocq theorem proves
that even equal application-identity projections cannot override the explicitly
supplied exact-source gate; its assumption query is part of the strict replay.

This is a necessary fail-closed producer/consumer equality, **not** proof
that the architecture occurrence produced the StageClosure, nor any faithful
Haskell-to-Rocq encoding, admitted native acceptance proposition, source /
assumption / erasure predecessor, `FinalArtifactCertified`, or release public
byte verification. Independent pinned final-delta review is outstanding.
No normative conformance case or historic audit finding is changed.
Independent Phase 1 audit-freeze verdict: **NOT YET**.

## 2026-11-06 — low-level declaration-only token cannot authorize final binding

The earlier `closeSourceManifestBinding` checks source declaration and closes an INT-002 manifest, but does **not** check the application semantic actuals against a canonical `ArchitectureInstanceDescriptor` or verify that instance's membership in the bundle. Both it and `closeSourceManifestBindingForInstance` returned the same opaque token, so the exported `bindProducedFinalAuthority` could consume the weaker declaration-only token without the high-level checked-instance wrapper.

The opaque `CertifiedSourceManifestBinding` now retains an optional `ArchitectureInstanceIdentity`. Declaration-only closure leaves it absent; only the stronger checked-instance path attaches the validated canonical occurrence after complete declaration, static actuals, and bundle membership checks. The exported binder rejects the unbound token with `SourceManifestInstanceNotBound` before checking the certified source or release. Upload and Steve negatives build the **same** manifest and matching independently accepted source/release as the checked producer, but prove the declaration-only token cannot bind; checked-instance positives retain the exact canonical occurrence. This is a necessary native producer gate, not authenticated occurrence-to-stage lineage.

Typed Rocq premises state separately that missing checked-instance-producer evidence blocks the stronger model boundary and that an explicitly supplied premise preserves only existing producer-consumer equalities. `Print Assumptions` is mandatory. No `Prop` is promoted to native proof acceptance; no Haskell-to-Rocq/nat encoding, instance-key-to-concrete-StageClosure provenance, complete `FixedFinalAuthorityAdapter` or `FinalArtifactCertified` is inferred. Source/assumption/erasure and final predecessors, faithful typed representations and injectivity, public release **bytes**, and independent pinned final-delta signoff remain open. LLVM/provider/runtime TCB and all original 244 normative cases remain unchanged; independent audit freeze verdict **NOT YET**.

## 2026-11-06 — preserve the full checked architecture descriptor in the native token

Previously `closeSourceManifestBindingForInstance` checked the complete `ArchitectureInstanceDescriptor` against the accepted `GenericApplicationAssurance` semantic actuals and verification bundle, then discarded the descriptor and kept only `ArchitectureInstanceIdentity`. The private `CertifiedSourceManifestBinding` now retains the **exact checked descriptor** (including declaration, parent/key lineage and semantic static bindings), and exposes a read-only `Maybe ArchitectureInstanceDescriptor` projection. Its existing canonical-identity accessor is derived from this retained descriptor; declaration-only closure retains neither. The exported final binder still fails closed for declaration-only tokens.

The strict Upload and Steve replay checks full descriptor retention as native typed equality, derives the same checked identity, and confirms declaration-only absence; existing changed/missing static argument, unregistered occurrence and substituted declaration negatives still run. Rocq adds a **conditional** separately typed descriptor-retention gate, preserving checked-producer premises while rejecting descriptor substitution even when a model's derived identities collide. The witness's descriptor-to-identity interpretation remains an explicit model parameter. `Print Assumptions` covers these lemmas and a logical collision counterexample. No native-to-Rocq total/injective representation is claimed or constructed.

This is lossless retention of already checked **source** descriptor inputs, not an authenticated assertion that the occurrence produced the independent concrete StageClosure. It does not equate the source/manifest's raw Systems digest and lowering root with normalized SystemsArtifactRevision, nor confuse the common Phase1StageContractRevision and final ClosedStageContractRevision. Stage predecessor authority, concrete representations/injectivity, public release-byte verification, independent pinned final-delta signoff and full `FinalArtifactCertified` remain open. No TCB changes, normative case changes or independent freeze credit. Verdict **NOT YET**.

## 2026-11-06 — exact descriptor retained across the final exported witness boundary

The checked source-manifest producer was hardened in #1600 to retain a complete `ArchitectureInstanceDescriptor`, but the next high-level `NativeFinalInstanceCorrespondence` constructor still discarded the checked descriptor and kept only `ArchitectureInstanceIdentity`. That loses the checked declaration, static semantic actuals, parent/key lineage before later native-to-Rocq representation. This separate successor keeps the complete descriptor in the **opaque exported final witness**, with `nativeCorrespondenceArchitectureDescriptor` as a read-only projection. The existing occurrence-identity accessor now derives identity from that descriptor; the StageClosure's `InstanceRevision` is still checked only by the separately optional revision gate and cannot establish occurrence-to-stage origin.

The strict Haskell Upload and Steve tests require the exact complete descriptor on both the independently produced checked source-manifest token and the final witness, plus derived canonical identity. Adversarial substitutions alter semantic static arguments and must be rejected by the checked producer; the existing witness continues to expose the original descriptor. Typed Rocq models the **two separate equality gates** (produced-to-token and token-to-exported) and proves exact transport only under those explicit externally supplied premises, with fail-closed substitution and noninjective-identity negative pressure. The three new theorems are in mandatory `Print Assumptions` replay. A model `Prop` does not count as native acceptance; no Haskell-to-Rocq encoding/injectivity is invented.

Still open: authenticated occurrence-to-actual-StageClosure production, concrete native-to-Rocq representation/injectivity and predecessor authority, complete `FinalArtifactCertified`, independently validated public release **bytes**, and independent pinned final-delta signoff. Raw Systems digest/lowering root are not normalized SystemsArtifactRevision; common Phase1StageContractRevision is not final ClosedStageContractRevision. Subject, instance, realization, and verifier profile remain independently typed. No TCB expansion, generated-output edit, normative-case change (the original 244 remain), historical audit overwrite, or independent freeze credit. **NOT YET**.

## 2026-11-06 — complete accepted source assurance retained at exported final witness

The checked source-manifest producer already retained the **complete accepted**
`GenericApplicationAssurance`, and both high-level and independently exported
low-level consumers required equality with the separately certified source
artifact. However, `NativeFinalInstanceCorrespondence` had exported only the
projected `GenericApplicationIdentity` inside its final authority. This
successor retains the **complete checked source-assurance object** in the opaque
final witness, sourcing it from the real produced source-manifest token. The
read-only `nativeCorrespondenceSourceAssurance` accessor prevents later
representation work from confusing equal application identities with equal
accepted reusable-body evidence. The manifest, raw Systems digest, lowering
root, normalized Systems revision, common/closed stage contracts and distinct
subject/instance/realization/profile coordinates remain unchanged and separate.

Strict Upload and Steve controls check exact equality of the source token,
accepted source, and exported final witness. Two independent checked-body
substitutions keep the same `GenericApplicationIdentity` but must fail the
existing exact source gate without modifying the accepted witness. The Rocq
model adds conditional three-boundary source-assurance transport and explicit
substitution rejection, including equal-identity negative pressure, with
`Print Assumptions` queries. The source identity projection and native
producer acceptances are still external typed premises: no Haskell-to-Rocq
totality, injectivity, or `nat` encoding is claimed.

This does **not** authenticate architecture occurrence-to-concrete StageClosure
production or discharge source/assumption/erasure/final predecessor authority.
No `FixedFinalAuthorityAdapter` or `FinalArtifactCertified` conclusion,
public release-byte verification, or independent pinned final-delta signoff
follows. Strict GHC, Rocq, LLVM and runtime/provider TCB remain unchanged.
The 244 normative cases and historical audit record are untouched;
independent Phase 1 audit-freeze verdict remains **NOT YET**.
