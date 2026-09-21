# R17/R18 follow-up: release archive and immutable-publication verification

## Audit source and scope

This slice addresses the two release-verification findings from **Phil Phase 1
follow-up audit — 2026-09-20 — 4cf858f**:

- **R17:** archive verification considered only regular members, so a later tar
  hardlink at an already-verified path could change the extracted file while the
  reader continued to validate the earlier regular bytes.
- **R18:** an existing non-draft GitHub Release was revalidated only by tag,
  asset names, the top-level bundle, and its checksum. The already-published
  platform archives, external release bindings, and notarization evidence were
  not downloaded and compared with the bundle that claimed to bind them.

The implementation base includes the R10/R16 landing at
`a68aa95a439f9e34e1ae4f9ac8572bf4fc9eb453` plus unrelated Surface proof
progress already on main.

## R17: one canonical archive tree

The release-bundle composer now derives one logical package tree from every
archive before trusting any selected member.

For both tar and ZIP packages it requires:

- exactly one package root;
- no absolute path, traversal component, empty component, or backslash path;
- no duplicate canonical member path, regardless of member type;
- ordinary directories only as non-file structure; and
- regular files only for package contents.

Tar hardlinks, symlinks, devices, FIFOs, and other special member types are
rejected. ZIP entries whose Unix file type is not regular are rejected,
including symlinks.

The same canonical tree is used for selected release members and for exact
`SHA256SUMS` coverage. The verifier therefore cannot validate one regular
`bin/philc` and later ignore another archive record that would replace that
path on extraction.

The permanent regression script contains:

1. a baseline regular tar package-tree acceptance control;
2. the audit's hardlink-replacement class at `pkg/bin/philc`;
3. duplicate regular tar members;
4. tar traversal;
5. ZIP symlink;
6. duplicate ZIP members; and
7. ZIP traversal.

This deliberately rejects ambiguous archive semantics rather than trying to
model platform-dependent link extraction.

## R18: verify preserved assets, not rebuilds

The composer adds a `--verify-existing-dir` mode. Given the exact published
asset directory, source commit, and package version, it:

1. verifies the top-level release-bundle checksum;
2. verifies Linux archive and archive-binding sidecars;
3. parses the Linux archive using the hardened R17 tree;
4. verifies Linux package manifest, internal release identity, compiler digest,
   handoff digest, archive binding, archive digest, and package-manifest digest;
5. repeats those checks for Darwin;
6. validates the published Darwin notarization-info JSON and its accepted
   submission ID;
7. requires both platforms to bind the same frozen handoff root;
8. reconstructs the canonical top-level release bundle from those **preserved
   downloaded assets**; and
9. requires the downloaded published bundle to equal that reconstruction
   byte-for-byte.

The existing-release branch now downloads the complete exact eleven-asset set
after its name-domain check and invokes that verifier. It no longer describes a
bundle-only check as byte-level release verification.

The normal PR bundle-composition job also invokes the same preserved-asset mode
on the freshly assembled release-assets directory. Thus the consumer
verification path is exercised before publication, even though the network
download branch itself only runs for an existing public release on main.

## Signing and immutability boundary

This does **not** compare a new signed Darwin rebuild with old signed bytes.
Developer-ID timestamps make that an invalid reproducibility requirement.
Instead, the preserved archive, binding, notarization evidence, and bundle are
validated against one another as the immutable publication record.

The server-side GitHub Release immutability policy remains external. This slice
does not assume it as the only integrity mechanism.

## Assurance boundary

This is release-composer and workflow implementation hardening. It does not
change proof source, generated kernels, or Certified-ledger status. Genuine
package smoke tests remain useful independent execution evidence and continue
to run.

At authoring, exact-head CI has not completed. The branch claims no successful
local execution beyond source review until CI records it.
