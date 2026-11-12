# P11 provisional candidate source and independent-auditor handoff — 2026-11-12

Control: [#1736](https://github.com/abiggerhammer/phil/issues/1736),
[maintainer re-triage](https://github.com/abiggerhammer/phil/issues/1736#issuecomment-6815422343).
This is **one nonpublishing review-evidence PR**, not another #1737 or #1584 implementation slice.
No Phase 1 freeze, new release tag, claimed external signoff, or TCB expansion is authorized.

## Fixed identities and claim boundaries

| Item | Immutable reference | Meaning |
| --- | --- | --- |
| Historical Phil public release source | `a9f2c745686d8ae1b923e21045554f4864956e76` | September 20 `phil-v0.1.0-phase1` source; 11 already published assets |
| Historical Steve public release source | `e7421fd1207af70833e6142979bf70d7fba3e8bf` | September 12 `steve-v0.1.1-phase1` source; 4 already published assets |
| P11 verifier merge / checkpoint parent | `d2cbe072964c9f7dbb7f37f5e31050151e804bb9` | #1737 landed, all 15 actual public bytes CI-hashed |
| **Provisional candidate REVIEW source** | **`13808408f9de0f67cefd6fa744f87d81a2d22fbb`** | Contains FSEM-02 #1738 after #1737; never follows moving main |
| Exact candidate source tree | `1e5847a146401e5d36ac4250a868e284ff4640fd` | Mandatory mismatch rejection |
| Candidate public tag and released bytes | **PENDING / ABSENT** | No staged file is a final signed browser-published asset |
| Out-of-band reviewer countersignature | **PENDING** | GitHub Actions execution is not independent review |

The archived historical September assets and their 15 CI-computed SHA-256s are
documented in [#1736 execution evidence](https://github.com/abiggerhammer/phil/issues/1736#issuecomment-6813138468).
The historical GitHub Releases API reported `immutable:false`; that does not
establish tampering or immutability. Those bytes precede November's
#1727/#1729/#1730/#1734 origin gates.

## Complete pinned source delta — generated evidence, not the capped API list

The audit-only [candidate-evidence workflow](../.github/workflows/phase1-p11-candidate-evidence.yml)
checks out **the above commit detached** with full history. It runs
`scripts/ci/audit-p11-candidate-delta.py` from the PR's separate audit-tools checkout.
The program fails if commit, tree, direct parent, baseline commit type or baseline
ancestry is wrong. For **each** historical source it emits:

- `{phil,steve}-to-p11-checkpoint.name-status.z`: raw complete NUL-delimited
  `git diff --no-ext-diff --no-textconv --find-renames=50% --name-status -z BASE PIN`.
  Includes rename source and destination, not merely 300 capped GitHub compare paths.
- `{phil,steve}-to-p11-checkpoint.paths.jsonl`: **all** names, status and
  overlapping review classes, JSON-escaped for non-ASCII and strange path names.
- `{phil,steve}-to-p11-checkpoint.full-binary.patch`: complete
  `git diff --no-ext-diff --no-textconv --binary --full-index BASE PIN`.
- `{phil,steve}-to-p11-checkpoint.commits.txt`: full ordered
  `git log --reverse --format='%H %P %s' BASE..PIN`.
- `p11-candidate-delta-summary.json`: exact commit/tree/parents, baseline
  identities, Git version, untruncated changed-record and commit counts,
  categorical counts, file sizes and **SHA-256 of every complete inventory**.

The log prints the full raw NUL inventory digest and summary JSON digest, to be
crosschecked against separately downloaded GitHub Actions evidence. The original
GitHub compare estimates (Phil 1,326 commits; Steve 2,426) are NOT exhaustive
changed-file evidence. **Do not substitute a main-relative diff or the truncated
300-file API response** for the generated two-baseline inventories.

Review classifications overlap intentionally:
`TCB-or-native-assurance` (verification/handoff/runtime/build inputs),
`assurance-or-audit`, `Rocq-representation-or-proof` (Rocq `.v`),
`release-pipeline` (release scripts/workflows), `CI-or-toolchain`,
`native-compiler-or-systems`, and `other`. These are triage aids, **not**
independent approval of proof discharge, trust completeness or semantic equivalence.
Auditors must inspect all relevant changed files and not infer safety from a label.

## First actually executed untruncated-delta receipt (source-only)

The first CI invocation at [Actions run #43164528303](https://github.com/abiggerhammer/phil/actions/runs/43164528303)
executed the complete detached-checkpoint inventory, not a 300-file compare:

| Baseline | All commits | Full changed records | SHA-256 of raw NUL inventory |
| --- | ---: | ---: | --- |
| Phil `a9f2c745...` | 1,326 | **1,301** | `23a9b2de0be4597a9dda79dc8654d0191e7018b187bb2fc9806c821064620524` |
| Steve `e7421fd...` | 2,426 | **1,922** | `1dbea12ec190a8655d0b8a73fa36110fb84c21bcf57ead2462dc0bfa0efaa9ef` |

Complete summary JSON SHA-256:
`8215b8febbb77d81051b3d19bdad33ca416a0c6f7d7bf8b682ef209ed58e96de`.
The [source-only artifact #13918898723](https://github.com/abiggerhammer/phil/actions/runs/43164528303/artifacts/13918898723)
contains both binary patches, full path/status inventories and exact commit ledgers.
It is CI-produced source evidence, **not independent auditor signoff**.
The other jobs in that first execution were still assessing staged bytes; any
failure there does not convert absent archives into verified candidate output.
A repaired-head rerun must also satisfy exact-head CI before merge.

## Nonpublishing candidate staging — attempted/observed bytes

Two isolated Actions runner jobs use the same detached source pin, with
`contents:read` only and no release, tag, signing or notarization credential.
They invoke the repository's existing **unmodified** distribution builders:

| Platform | Builder outputs and proposed audit artifact | Authority |
| --- | --- | --- |
| x86-64 Linux | Phil `.tar.gz`, `.sha256`, `.release` and `.release.sha256`; Steve `.tar.gz`/`.sha256`; `p11-source-13808408f9de-linux-unsigned-structural` | Provisional, not public |
| Apple Silicon macOS | unsigned Phil `.zip`/`.sha256` and Steve `.tar.gz`/`.sha256`; `p11-source-13808408f9de-darwin-unsigned-structural` | **No Developer-ID signature, Gatekeeper/notarization acceptance or quarantined-user proof** |
| Both when built | `files.sha256`, `components.sha256`, toolchain/clang version, full `SHA256SUMS`, built `philc`/`steve` byte hashes, unpacked `./smoke-test.sh` logs | CI-produced staging only |
| Both when emitted | `diagnostic-steve-choice.ll` and `diagnostic-steve-choice.o`, hashed separately | **Diagnostic rebuild only; cannot prove equality to separately linked native Steve executable object** |

The Darwin builder's inherited internal package identifier may say
`0.1.0-phase1`; this is a legacy builder output name, **not a nominated public
version or final candidate tag**. The workflow artifact names are explicitly
provisional and tied to the source SHA. Failed builds require reporting missing
bytes and job logs; never insert guessed hashes.

The release scripts compile native binaries independently of P7's producer.
Steve's `steve.release-package` derives from legacy INT-005 structural fixtures.
This does **not** establish a source K/I -> actual published Steve/philc executable
chain. The native constructor-private P2/P6/P7/#1734 package result is a separate,
stronger proof boundary; no fake certificate is minted or inferred from hashes.
The preexisting Phase 1 TCB remains disclosed and unchanged.

## Reproduce without publishing or privileged credentials

After cloning `abiggerhammer/phil` into an audit-tools checkout at the exact
reviewed PR/merge SHA:

```sh
git clone https://github.com/abiggerhammer/phil.git pinned-source
git -C pinned-source checkout --detach 13808408f9de0f67cefd6fa744f87d81a2d22fbb
git -C pinned-source fetch --unshallow 2>/dev/null || true
python3 scripts/ci/audit-p11-candidate-delta.py --self-test
python3 scripts/ci/audit-p11-candidate-delta.py \
  --repo pinned-source --out /tmp/p11-complete-delta
(cd pinned-source && bash ../scripts/ci/audit-p11-candidate-stage.sh linux \
  /tmp/p11-auditor-linux)
```

Run the last step on x86-64 Linux with GHC 9.6.7, Cabal and LLVM/Clang 18.
On native arm64 macOS with GHC 9.6.7 and Homebrew LLVM 18, replace `linux`
with `darwin`. The staging script itself fails closed for wrong commit/tree,
wrong parent, wrong platform, incomplete checksum sidecars, missing smokes and
unavailable toolchains, rather than claiming a valid binary. The diff script's
self-tests reject fake pins, wrong tree/parent and truncated NUL statuses;
the staging script includes a corrupted SHA-256-sidecar negative control.

For **independent historical published-byte replay**, use the already merged
auditor command with fresh downloads, not an Actions artifact:

```sh
python3 scripts/release/audit-p11-public-bytes.py \
  --download-dir /tmp/p11-independent-september \
  --evidence /tmp/p11-independent-september.json
```

Run on actual fresh GitHub browser-download payloads; compare the 15 SHA-256
records with an *out-of-band* retained audit record, checksum sidecars and
archive/notary/TCB validation. See [P11 baseline instructions](p11-release-byte-audit-2026-11-12.md).
For an **eventual newly published candidate**, a new authorized URL/name/hash
inventory and independent fresh download are still required; there are no
candidate browser URLs today.

## Mandatory external release-review/countersignoff checklist

- [ ] Inspect both complete NUL inventories, JSON path classifications, binary
  patch and exact `BASE..PIN` full commit ledger; independently reproduce SHA-256s.
- [ ] Review TCB, native↔Rocq, assumption/erasure/discharge and release-pipeline
  modifications against separate P8/P9/P10 owners; do not self-approve them.
- [ ] Obtain staged Linux/Darwin bytes if built, independently hash archives,
  sidecars, executables, LLVM/object diagnostics, complete `SHA256SUMS`,
  toolchain metadata, package TCB and smoke transcripts.
- [ ] Review missing or failed platform builds as missing evidence. Darwin
  signed/notarized/quarantine-intact outputs remain **PENDING** without separate
  authorized release-signing procedures.
- [ ] Resolve actual executable-byte relation to checked source K/I, manifest,
  whole StageClosure, complete CertifiedRelease and LLVM/trust; **NOT PROVEN**.
- [ ] Obtain maintainer-approved final source/tag and exact final public bytes
  via separate authorization, then independently re-download/hash.
- [ ] Obtain out-of-band independent auditor identity, written acceptance,
  authenticated/countersigned digest and complete final delta.
- [ ] Obtain separate P8/P9/P10 signoffs and final freeze decision.

**Final candidate bytes: PENDING. External reviewer: UNASSIGNED.
Independent release signature and final delta: PENDING.
`FinalArtifactCertified`: UNPROVED. Independent Phase 1 freeze: NOT YET.**
Issue #1584 stays OPEN. Original 244 normative conformance cases are unchanged.
