# P11 v2 — immutable provisional source, unsigned staging and independent-auditor packet

Control: [issue #1736](https://github.com/abiggerhammer/phil/issues/1736#issuecomment-6869671802).
This is PR **2 of 2** in a bounded audit-only tranche. Do not tag, sign, notarize,
publish, overwrite, self-certify, or ratify this candidate. The 244 Phase 1
normative conformance cases, original TCB kinds, P8/P9/P10 obligations,
and historical audits remain unchanged.

## Source provenance (must be exact)

| Role | Full Git commit | Tree / meaning |
| --- | --- | --- |
| **NEW provisional REVIEW checkpoint** | `9c7d48bc7c5f85b241df9343136c104c3af7a22b` | tree `575abbe2f916c37775e7baba9a35a8235ca0b6da`; **actual #1767 merged main**, not its PR head or synthetic Actions merge |
| First parent | `3d01a717dac361aba0b0eacd4bde1058b9793937` | former main |
| Second parent | `b90d1c1a2ca54d110200a4129dc55ff08cd8a755` | #1767 tested head |
| REJECTED old checkpoint | `13808408f9de0f67cefd6fa744f87d81a2d22fbb` | historical rejection; immutable, not repaired retroactively |
| September Phil source | `a9f2c745686d8ae1b923e21045554f4864956e76` | `phil-v0.1.0-phase1`; previously CI-audited 11/11 public assets |
| September Steve source | `e7421fd1207af70833e6142979bf70d7fba3e8bf` | `steve-v0.1.1-phase1`; previously CI-audited 4/4 public assets |

#1767 signed-claim correction: [23/23 exact-head checks, 20/20 workflows](https://github.com/abiggerhammer/phil/pull/1767);
[protected merge intent](https://github.com/abiggerhammer/phil/actions/runs/43548685320) successful.
The new native, typed UNSIGNED-only Darwin basis differs from the signed basis,
retains four trust kinds and checked names/revisions, and does not change
privileged signed/notary release procedures. The pinned source is a **review
snapshot**, not final released bytes, a signature, or a frozen complete proof.

## Complete source delta (three independent fixed baselines)

`scripts/ci/audit-p11-v2-complete-delta.py` checks the literal commit,
whole Git tree, both parents and base ancestry. `--self-test` covers wrong
commit/tree/parent order, malformed NUL records, and classification controls.
The **new** audit-only workflow `phase1-p11-v2-candidate-evidence.yml`
checks out the pinned source in a separate detached directory with full history.

Run with ordinary Git and Python 3:

```bash
git clone https://github.com/abiggerhammer/phil.git phil-audit
cd phil-audit
git checkout --detach 9c7d48bc7c5f85b241df9343136c104c3af7a22b
git fetch --unshallow 2>/dev/null || true
python3 scripts/ci/audit-p11-v2-complete-delta.py --self-test
python3 scripts/ci/audit-p11-v2-complete-delta.py --repo . --out /tmp/p11-v2-delta
sha256sum /tmp/p11-v2-delta/*
```

The script emits, for **Phil September → pin**, **Steve September → pin**,
and **rejected old checkpoint → pin**, separate COMPLETE
`*.name-status.z` NUL-terminated rename-aware path/status inventories,
`*.paths.jsonl` full review-classified path lists,
`*.full-binary.patch` complete binary-aware diffs,
`*.commits.txt` full commit provenance, and
`p11-v2-complete-delta-summary.json` with each file's SHA-256, byte length,
all changed-record/commit counts, source commands and classifications.
GitHub's capped 300-file compare is **not** an acceptable replacement.
The actual output SHA-256 values must be copied from executed exact-source CI
and independently recomputed by a reviewer; **PENDING until executed**.

Sensitive review classes are nonexclusive:
TCB/native assurance; audits/handoff; Rocq representation/proofs;
release pipeline; CI/toolchains; native compiler/Systems; other.
These labels prioritize review; they are NOT proof that a change is safe.

## Real unsigned Linux and Apple Silicon staging

Run audit tools and pinned source in **separate checkouts**. The workflow uses
`contents: read` and has no signing, publication or release permissions.
GHC 9.6.7, LLVM/clang 18, and Mac deployment floor `11.0` are enforced
before Cabal builds. Its source pin/tree/parents are fail-closed. It stages:
`phil-0.1.0-phase1-x86_64-linux.tar.gz`,
`phil-steve-0.1.1-phase1-x86_64-linux.tar.gz`,
`phil-0.1.0-phase1-aarch64-apple-darwin.zip`, and
`phil-steve-0.1.0-phase1-aarch64-apple-darwin.zip` (actual filename in
the builder/receipt is authoritative). These names are inherited package
formats, **not** newly published tags or final versions.

Each platform must pass actual FULL extracted Phil and Steve native smokes.
Archive .sha256 / .release binding sidecars, staged component digests,
TCB.txt, BUILD-INFO, compiler bytes, handoff and SHA256SUMS must be present
and consistent as applicable. On Darwin, the exact unsigned build-toolchain
basis must appear, the signed assertion must be absent, four TCB entries
must match the machine record, and a changed handoff must fail the unchanged
packaged smoke. An emitter self-test rejects a forged signed basis. A separate
digest corruption test rejects a changed SHA. The workflow retains output
archives, sidecars, diagnostic LLVM text/object, hashes, build logs,
smoke result and source/toolchain information.

**Important distinction:** diagnostic `diagnostic-steve-choice.o` is an
independently rebuilt LLVM object, not the object linked into shipped
`bin/steve`. Historical Steve `steve.release-package` is a structural
INT-005 fixture independently produced from the executable. No actual
checked K/I → compiled public `philc` or Steve executable lineage is proven
by staging/checksums or the P7 origin type. The printed `source-head.txt`
MUST equal the pinned actual merged source, not Actions' synthetic PR merge;
the audit-tools checkout can separately identify the synthetic checkout.

## Reviewer download and reproduction (once Actions finishes)

Read the run ID and all job conclusions from the new v2 workflow on the
**exact PR head**. Download the artifacts in a fresh external environment:

```bash
gh run download RUN_ID -R abiggerhammer/phil \
  --name p11-v2-full-three-baseline-delta-9c7d48bc7c5f \
  --dir /tmp/p11-v2-review/delta
gh run download RUN_ID -R abiggerhammer/phil \
  --name p11-v2-source-9c7d48bc7c5f-linux-unsigned-structural \
  --dir /tmp/p11-v2-review/linux
gh run download RUN_ID -R abiggerhammer/phil \
  --name p11-v2-source-9c7d48bc7c5f-darwin-unsigned-structural \
  --dir /tmp/p11-v2-review/darwin
```

Independently hash **downloaded** bytes and compare to `files.sha256`,
`components.sha256`, archive `*.sha256` and the complete delta JSON
receipts. Re-run the merged P11 historical-asset verifier separately against
the actual public September assets; those are different bytes and source.
Reproduce package unpack/full smoke on native Linux/macOS and the tamper
negative. Verify the full source tree and complete diff inventories, compare
both TCB profiles and signed-vs-unsigned identity, inspect actual toolchain
versions in `toolchain.txt`, and inspect archived `*.ll` / `*.o` without
confusing diagnostics with shipped objects. Check signed/notarized evidence
only when an independently authorized final release exists.

## Human countersignoff checklist (all initially PENDING)

- [ ] CI exact pinned-source three-baseline full delta executed and SHA-256s recorded.
- [ ] CI both OS native Phil and Steve full package smokes, SHA/sidecar and
      tamper negatives executed and four actual archive SHA-256s recorded.
- [ ] External auditor independently downloads fresh actual artifacts, hashes
      all bytes, validates archive safety and complete changed paths, and
      reproduces verification independently (not a CI log signoff).
- [ ] Maintainer accepts/rejects the **provisional** checkpoint following
      TCB, release-pipeline, native/Rocq and assurance delta review.
- [ ] New final signed/notarized public release/tag/bytes, toolchain and
      out-of-band cryptographic/notary evidence established in a separate
      expressly authorized process.
- [ ] Actual checked P2/P6/P7/#1734 accepted K/I origin is bound to the
      selected whole *shipped* compiler and Steve executable bytes.
- [ ] P8, P9, P10, `FinalArtifactCertified` and independent final delta/freeze
      receive their separate competent approval.

**Current status:** v2 source checkpoint PINNED FOR REVIEW ONLY; signed
and notarized output ABSENT; new final published candidate bytes ABSENT;
external independent auditor identity/acceptance/signature PENDING;
P8–P10 UNPROVED; `FinalArtifactCertified` UNPROVED; independent
Phase 1 freeze **NOT YET**. Keep issues #1736 and #1584 OPEN. No third PR
or autonomous final release is authorized.
