# Phil Phase 0 evidence bundles in Steve

This directory defines a branch-only, deterministic packaging convention for preserving the frozen Phil Phase 0 evidence set in Steve.

The bundle does **not** make Steve part of the Phase 0 trusted computing base and does not create proof authority. Every proof object, certificate, target artifact, runtime ABI description, and assurance manifest must already have whatever authority it independently earned. Steve only preserves the exact bytes and a content-addressed manifest naming them.

## Root object

A bundle root is the SHA-256 digest of one canonical UTF-8 JSON manifest. The manifest has exactly four fields:

```json
{
  "format": "phil-steve-phase0-evidence-v1",
  "objects": [
    {
      "kind": "proof-certificate",
      "name": "PHIL-LLVM-CERT-010",
      "sha256": "...",
      "size": 1234
    }
  ],
  "phase": "0",
  "source_revision": "<frozen git revision>"
}
```

Object entries are sorted lexicographically by logical `name`. The JSON encoding uses sorted object keys, no insignificant whitespace, UTF-8, and exactly one trailing newline. The SHA-256 of those exact bytes is the bundle root.

The manifest is itself installed into Steve as an ordinary content-addressed object. Therefore one digest names the entire reachable evidence set.

## Input spec

`scripts/steve_phase0_bundle.py build` consumes a small local JSON spec. The spec deliberately contains filesystem paths, but those paths are not copied into the canonical manifest and therefore do not affect the bundle identity.

```json
{
  "source_revision": "<frozen git revision>",
  "objects": [
    {
      "name": "phase0-source-archive",
      "kind": "source",
      "path": "artifacts/phase0-source.tar"
    },
    {
      "name": "PHIL-LLVM-CERT-010",
      "kind": "proof-certificate",
      "path": "artifacts/PHIL-LLVM-CERT-010.cert"
    }
  ]
}
```

Logical names must be unique. Two logical entries may legitimately name the same content digest if their authoritative bytes are identical.

## Store layout

The host-side reference tool uses the deliberately boring layout:

```text
<store>/objects/sha256/aa/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
```

where `aa...` is the SHA-256 digest. Installation is no-clobber: the tool writes a complete temporary file and then uses an atomic hard-link create into the final object name. If the object already exists, the bytes must compare equal. A same-digest/different-bytes observation is reported rather than overwritten.

This mirrors the Steve 0 `install_if_absent` architecture; the Python tool is only a host-side reference assembler for the evidence package, not the eventual Phil implementation of Steve.

## Build and verify

From the repository root:

```text
python3 scripts/steve_phase0_bundle.py build \
  --spec /path/to/phase0-bundle.json \
  --store /path/to/steve-store \
  --root-out /path/to/PHIL-PHASE0.root
```

The command prints and optionally records a handle of the form:

```text
sha256:<64 lowercase hex digits>
```

Verification starts from that handle and checks the root manifest plus every directly referenced object:

```text
python3 scripts/steve_phase0_bundle.py verify \
  --store /path/to/steve-store \
  --root sha256:<root>
```

The verifier rejects a missing object, digest mismatch, size mismatch, malformed manifest, duplicate logical name, noncanonical ordering, or noncanonical JSON encoding.

## Freeze procedure

Do not mint the real Phase 0 root before Phase 0 is frozen.

At the freeze point:

1. identify the exact frozen Git revision;
2. collect the authoritative source/archive, Core/Systems/LLVM artifacts, runtime ABI descriptions, checked Rocq sources and proof objects, proof certificates, assurance manifest/certificates, and retained runtime/integration evidence chosen for the release record;
3. write the final input spec with stable logical names;
4. build the Steve bundle;
5. verify it from the emitted root in a fresh store or after transfer;
6. record the root digest as the content-addressed handle for the frozen Phase 0 evidence package.

The root is an archival/retrieval identity, not a new statement that every reachable object is logically sufficient, trustworthy, or proof-authoritative. Those claims remain the responsibility of Phil's assurance machinery.

## Branch status

This machinery stays on `steve/architecture-sketch` until the existing Steve branch handoff criteria are met. No Phase 0 `main` changes are required to prepare the bundler, and no provisional Phase 0 root is checked in.
