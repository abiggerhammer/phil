# #1584: one authorized downstream final-origin consumer migration

Maintainer re-triage 2026-11-12. Historical P2 #1727, P6 #1729 and
P7 #1730 are merged (3/3); this is **the single additional authorized
follow-up (1/1)**. It does not reset that budget. Issue #1584 remains OPEN.

## Concrete final-claim/structural call graph

| Exact consumer / route | Before | After and assertion |
|---|---|---|
| `Phil.Verification.ReleasePackage.buildCertifiedReleasePackage` and `renderCertifiedReleasePackage` | Plain `AssuranceLedger -> CertifiedReleaseArtifact -> Either ... CertifiedReleasePackage`, render sidecar; a structural result was callable by a final-claim-named API | **Migrated final-origin gate**: requires sealed `AcceptedVerifiedFinalOrigin` from P2/P6/P7; returns opaque `VerifiedOriginReleasePackage`; renderer emits checked K/I plus package ID and original structural body. A separately certified artifact is **compile-negative** at this entry. |
| `buildStructuralReleasePackage` and `renderStructuralReleasePackage` | Former body of certified package APIs | **Explicit structural-only** manifest/ledger, stage, lowering, LLVM/TCB metadata formatting; bytes unchanged. Cannot mint the opaque strong package. |
| `test/Phase1INT001WitnessE2EMain.hs` | Genuine Upload/Steve ordinary source/Core → private P2 event → reconstructed P6 whole StageClosure → independently accepted P7 manifest/source/release | **Migrated strong package test**: `acceptVerifiedFinalOrigin` precedes the new package builder. Tests K/I and full manifest/LLVM target retention. Existing P7 source/manifest/K/stage/release/LLVM/trust substitution tests replay alongside. |
| `test/Phase1INT005ReleasePackageMain.hs` → `scripts/ci/phase1-int-005-release-package.sh` | Historical Upload/Steve independently constructed manifest/stage → `certifyConventionalFixture` → package | **Structural only**: intentionally calls weaker named formatter; preserves format/LLVM/native smoke. Script also runs the external-client *compile-negative* old-artifact-to-strong-builder attempt. |
| `test/Phase1INT005EmitCertifiedReleaseMain.hs` → `scripts/ci/phase1-int-005-native-release-smoke.sh` | Old independent witness → `certifyConventionalFixture` → LLVM | **Structural LLVM replay only**; cannot authenticate checked occurrence K. Explicit weaker-source comment. |
| `test/Phase1TargetAArch64AppleDarwinReleasePackageMain.hs` | Independently certified Darwin target/trust fixture | **Structural only**: retains cross-target checks, weaker package builder/renderer. |
| `audit/upload-artifact-package/ReleaseAssociationReview.hs` | Historical fixed-witness/cross-stage and LLVM/ledger checks | **Structural-only audit**: retains all historical rejection cases on weaker API. |
| `scripts/release/build-steve-phase1-package.sh` → `steve.release-package` / `TCB.txt` | Public packaged structural INT-005 sidecar from old fixture | **Residual publication path, unchanged**: the public script emits a separate conventional INT-005 structural `steve.release-package` and `TCB.txt`, not a sealed P7 checked-K/I origin certificate. The existing use of “certified” describes structural INT-005 closure, not verified occurrence provenance. Public-byte migration remains separately owned. |
| `Phil.Handoff.Phase1AssuranceClosure.derivePhase1ResidualTCB` / INT-007 | `CertifiedReleaseArtifact` → manifest/TCB roundtrip | **Structural-only** declared TCB and independent manifest parsing; does not mint stronger authority. |
| `certifyReleaseArtifact`, `bindNativeFinalAuthority`, `bindProducedFinalAuthority`, `closeNativeFinalInstanceCorrespondence` | Separately callable structural accepted-object consistency and coordinate projections | **Structural-only**, return neither `AcceptedVerifiedFinalOrigin` nor strong package; preserve independent bounded tests. Do not interpret as checked source producer. |
| `scripts/release/build-phil-phase1-package.sh` / INT-011 `DistributionRelease` | Public `philc` compiler bytes, handoff manifest, archive digests, declared distribution TCB | **Different distribution/byte authority**, NOT the P7 Upload/Steve occurrence; independent P11 work; no false conversion to P7. |

## Actual authority and adversarial boundaries

The constructor-private `AcceptedVerifiedFinalOrigin` is minted only by
`produceVerifiedFinalOrigin` + `acceptVerifiedFinalOrigin` from the genuine
ordinary-source P2 and whole-stage P6 event and complete P7 independently
checked source/manifest/whole release, LLVM target/text and declared trust.
The migrated package API never accepts plain `CertifiedReleaseArtifact`.
The new strong tests execute verified Upload and Steve source-to-package
positives. Legacy-artifact entry fails **Haskell static typing** in
`Phase1INT005FinalOriginPackageTypeNegative.hs` (validated by the INT-005
script). Same-I/different-K and incorrect source/manifest/stage/release,
changed LLVM target and trust are **P7 runtime rejection sites**, not a
signature, and the actual strong package consumer uses only their accepted
output. Strong renderer records K/I alongside its internal package ID but
cannot attest post-publication bytes.

**Remaining known public-release question**: the actual Steve release script
still emits a *structural-only* INT-005 package from a different legacy
stage/LLVM witness. It must not be called P7-certified. If final-origin provenance
is required for those particular published bytes, the upstream source,
compiled runtime-choice LLVM/object and package builder need the same-event
proof and an explicit separately authorized release-pipeline migration. A
single syntactic P7 wrapper would be false authority. This PR closes the
higher-priority named final-origin API bypass but does not discharge that
published-byte obligation. The historical Steve public README/TCB wording
remains unchanged: its “certified” adjective denotes the standalone structural
INT-005 envelope, not P2/P6/P7 origin provenance. The protected merge workflow
admits only the trusted INT-011 PR-only `publish` skip: changing the separate
Steve release script triggers a distinct non-whitelisted `publish` skip. This
single follow-up does not change release policy or weaken its protection.

## Evidence and independent gates

Merged #1730 head `1bd59b4a53308ab842225e83801298af43a065f9`
had 103/103 workflow successes, 208 successful checks plus one trusted
nonrequired PR-only INT-011 publish skip, protected merge
`5074ce438260856d4afd91271265f157100d20a1`. P7 reconciled in
append-only readiness report. This new PR is **not credited until its own
exact-head checks and protected merge complete**. Supplementary Matrix P7
evidence requires independently recorded external Sheet row; the original
244 normative cases are not edited.

P8 recursive SemanticForm/Unicode/Map/Set accepted native↔Rocq
representation, P9 predecessor/evidence/erasure/discharge, P10 conditional
FixedFinalAuthorityAdapter and `FinalArtifactCertified`, P11 public
release-byte/checksum and pinned final delta all **remain open**.
No new TCB assumption, full native↔Rocq theorem or independent audit
freeze is claimed. **Freeze: NOT YET.**
