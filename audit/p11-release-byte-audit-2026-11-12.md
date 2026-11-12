# P11 public-byte audit: September baselines vs Phase 1 final candidate

Issue: [#1736](https://github.com/abiggerhammer/phil/issues/1736).
This is a **release-byte audit**, not the #1584 native implementation lane.
This document is append-only scoping/evidence until a CI run actually downloads and
hashes every browser asset; no result from an unmerged PR is certified.

## Exact historical baseline metadata (not an independently observed byte hash)

| GitHub tag | Published UTC | Lightweight tag/source commit | Assets | API immutable |
| --- | --- | --- | ---: | --- |
| [phil-v0.1.0-phase1](https://github.com/abiggerhammer/phil/releases/tag/phil-v0.1.0-phase1) | 2026-09-20 17:31:05 | `a9f2c745686d8ae1b923e21045554f4864956e76` | 11 | false |
| [steve-v0.1.1-phase1](https://github.com/abiggerhammer/phil/releases/tag/steve-v0.1.1-phase1) | 2026-09-12 08:08:04 | `e7421fd1207af70833e6142979bf70d7fba3e8bf` | 4 | false |

All 15 exact names, byte sizes and reported SHA-256 hashes from the 2026-11-12
GitHub Releases API inventory are **frozen reference values** in
`scripts/release/audit-p11-public-bytes.py`. These are API-reported *expectations*,
not independent signoff or evidence of immutable GitHub storage. A discrepancy
is a review trigger, **not automatically proof of tampering**.

### Reproduction (unprivileged Linux/macOS shell, Python 3.10+)

Run from the repository checkout at an audited commit:

```sh
python3 scripts/release/test-phase1-release-bundle-verifier.py
python3 scripts/release/test-p11-public-bytes.py
python3 scripts/release/audit-p11-public-bytes.py \
  --download-dir /tmp/phil-p11-public-bytes \
  --evidence /tmp/phil-p11-public-byte-evidence.json
```

The final command resolves each tag and its exact commit from the public GitHub
API; checks the complete named asset list; and **downloads every actual
`browser_download_url` payload**. It hashes the downloaded stream and
independently rereads the preserved file. It checks exact size, the frozen
API baseline, and each published checksum sidecar. It invokes the existing
`compose-phil-phase1-release-bundle.py --verify-existing-dir` logic for the
11 Phil assets, including Linux/Darwin handoff identity, archive binding,
notarization record, exact compiler/package checksums and reconstructed
top-level release bundle.

The Steve verifier rejects missing, unexpected, duplicate, non-canonical,
link and path-traversal archive members; requires executable `steve`,
`philc`, and smoke script; verifies exact full-tree `SHA256SUMS` coverage
and both published archive sidecars; checks LLVM target, all six TCB records,
verbatim `TCB.txt` correspondence, and cross-platform ordinary source-file
identity. It **does not** treat historical `steve.release-package` as a
checked-source-occurrence certificate or assert its digests bind the independently
compiled public Steve executable bytes.

To replay on independently fetched bytes without a GitHub API request:

```sh
python3 scripts/release/audit-p11-public-bytes.py \
  --offline --download-dir /tmp/phil-p11-public-bytes \
  --evidence /tmp/phil-p11-replay-evidence.json
```

The input directory must have exactly the two tag-named subdirectories with
all and only the 15 published file names. Preserve the **full actual files**,
not GitHub API JSON/digests. The script fails closed on changed sizes/digests,
missing or added files, bad paths/links/modes, mismatched sidecars, wrong
LLVM target/TCB, false P7-origin claims, or cross-platform Steve source
mismatch. Negative tests exercise these classes with synthetic bytes; a
passing negative unit test is not evidence that historical public bytes
were downloaded.

The audit-only GitHub Actions job (if executed) provides **CI-observed
public-byte hashes**, not signed independent-auditor testimony. The resulting
JSON and exact run URL must be attached to the issue after the run succeeds.
An independent auditor must separately acquire both release download sets,
verify against an **out-of-band** digest, review toolchain/TCB signatures, and
countersign the candidate/delta.

## Authority and release-byte boundaries

| Boundary | Status/meaning |
| --- | --- |
| Phil September standalone compiler archive / notarization / bundle | Structural distribution byte checks, independently hashable |
| Steve September Linux/Darwin public archive and sidecars | Structural-only INT-005 release package; its actual binaries are separate products |
| P2/P6/P7 sealed K/I + complete StageClosure + complete CertifiedRelease | November native accepting-path result; **not present in September assets** |
| #1734 strong `VerifiedOriginReleasePackage` gate | Native producer-to-package consumer, **not published executable-byte provenance** |
| Public downloaded binary ↔ exact checked K/I | **NOT PROVEN** |
| Historical independent audit | Preserved; not superseded by a new CI result |
| `FinalArtifactCertified` / native↔Rocq final authority | **UNPROVED (P8/P9/P10 other owners)** |

## Pinned Phase 1 final-candidate / delta checklist

This checklist must **not** be silently filled from historical release metadata:

| Item | Current state |
| --- | --- |
| Future candidate exact source commit / immutable tag | **UNPINNED** |
| Comparison base | #1734 merge `745bab20385cbc7aef0b61fa7944aef7bcea4064` is the last known strong-package integration baseline; not an approved final-candidate pin |
| Complete final candidate git diff and exact build provenance | **PENDING** |
| Future platform asset names, browser URLs, downloaded SHA-256 and byte sizes | **PENDING** |
| GHC, Cabal, LLVM 18, native runtime, Apple signing/notary, OS/ABI and TCB review | **PENDING independently reviewed signatures** |
| Correct checked source occurrence K/I, manifest, StageClosure and release/LLVM/trust link to actual produced distribution bytes | **NOT PROVEN** |
| Independent auditor identity, downloaded-byte verification report and signed delta | **PENDING** |
| Owner-approved release publication / immutability policy | **PENDING**; current historical releases report `immutable: false` |
| FinalArtifactCertified | **UNPROVED** |
| Independent Phase 1 freeze | **NOT YET** |

No historical asset is rewritten, re-tagged, republished or promoted to a
November final-origin release by this P11 engineering check. No change to the
244 normative conformance cases, historical audit or Phase 1 TCB is authorized.
A single PR is budgeted for the engineering verifier and then maintainer review
is mandatory even if every CI test succeeds.
