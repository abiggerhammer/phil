# Source-to-manifest producer binding — bounded verification continuation

**2026-11-05** · Lineage: D-ARTIFACT-MANIFEST-REFLECTION-01 and the NR-D06 / #1577 native final-authority adapter.

## Actual producer

The existing `Phil.Verification.ManifestClosure.closeVerificationBundle` produces a checked `AssuranceManifest` from a canonical `VerificationBundle`, assurance policy, verification context, ledger and selected evidence/assumptions. It validates bundle policy and architecture identity, graph/ledger obligations, evidence and closure constraints and the manifest verifier. The output carries a content-derived ID.

However, `GenericApplicationAssurance` identity is not stored literally in `AssuranceManifest`; earlier `ExpectedSourceManifestAssociation` was an ordinary caller-provided pair of an application identity and a manifest ID. Merely comparing that pair to two accepted objects is insufficient to demonstrate a shared producer.

## Bounded implementation

New `Phil.Verification.SourceManifestBinding.closeSourceManifestBinding` reuses the actual `closeVerificationBundle` producer. It checks that an accepted `GenericApplicationAssurance` lineage's declaration key, interface revision and definition revision **exactly occur in the same VerificationBundle declaration set** from which it closes the manifest. The result is an opaque `CertifiedSourceManifestBinding` containing the matched application identity and the actual newly closed manifest. The caller cannot construct its data constructor or substitute a free-standing identity pair through this interface.

`bindProducedFinalAuthority` requires the original produced manifest to equal the independently accepted `CertifiedReleaseArtifact`'s manifest **in full**, then invokes the #1577 accepted-object native final-authority binding for the accepted source/application and release witnesses. It continues requiring the complete retained StageClosure to agree.

## Direct tests

The existing INT-005 native test constructs a genuine accepted generic source via VER-009, a verification bundle via VER-012, a closed manifest via this new producer, an exact certified release from that manifest, and a source/artifact pair from the same stage for both Upload and Steve. It compares the projected native source, manifest and raw Systems coordinates.

Negative cases reject an unlisted source declaration, a bundle/verification-context architecture mismatch, and substitution of a different certified manifest. Existing source, stage, manifest and LLVM/trust tests remain.

## Explicit assumptions that are **not** closed

- Membership of a declaration does **not** prove that generic semantic arguments match an exact architecture instance or that the complete application is authorized by every declaration in a source bundle. This is checked **declaration-level producer correspondence**, not whole-source application linkage.
- This does not make mutable Haskell `VerificationBundle` constructors inaccessible. The intrinsic/source producer and competence of its inputs remain part of the trusted prior verification interface.
- No native-to-Rocq representation proof is generated. Digest/Text/source identity equivalence to Rocq `nat` is still an explicit model-correspondence premise.
- Assumption/erasure producer authority and provider competence remain inherited; the release-publication byte gate and independently pinned final review remain separate.
- These are submitted tests until green exact-head CI, not a claim of a completed independently audited Phase 1 freeze.

The historic independent review corpus and 244 conformance cases are unchanged.
