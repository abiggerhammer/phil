# INT-007 Phase-1 handoff manifest v1 — integrity spine

Matrix case **INT-007** requires the Phase-1 freeze to publish one versioned,
machine-readable handoff manifest whose artifacts can be consumed without
Haskell-private object state. This slice establishes the manifest and its exact
byte-integrity boundary. It does **not** claim INT-007 is complete.

## Format

`handoff/phase1/manifest-v1.tsv` begins with:

```text
PHIL-PHASE1-HANDOFF-MANIFEST-V1
artifact_id<TAB>artifact_kind<TAB>repository_path<TAB>sha256<TAB>governing_authority
```

Each artifact row carries:

- a stable handoff artifact ID;
- a bounded portable artifact-kind vocabulary;
- a repository-relative POSIX path with no absolute/traversal form;
- the exact `sha256:<64 lowercase hex>` of the referenced bytes; and
- one or more semicolon-separated exact authority references of the form
  `matrix:<Case-ID>` or `certified:<Obligation-ID>`.

Artifact IDs and repository paths are unique. Authority references within one
artifact row are unique. Unknown kinds, malformed paths, malformed digests,
malformed authority references, duplicate IDs/paths, unreadable artifacts, and
digest mismatches fail closed.

The encoding is Phase-1 handoff/test infrastructure. It is not a promise that
this TSV syntax or these stable IDs become permanent Phil ecosystem syntax.

## First admitted inventory

The first slice content-addresses the already-portable roots needed to bootstrap
the handoff:

1. the exact Grammar-v1 EBNF bound by SURF-006;
2. the positive parser corpus manifest governed by SURF-002;
3. both persisted SURF-010 SourceBundle/lineage carrier fixtures; and
4. the portable negative-corpus root manifest governed by INT-004.

The permanent gate also requires a bijection with the admitted inventory, so a
row cannot silently disappear or an unreviewed row silently appear.

## Persisted witness SourceBundles

The second slice adds exact portable descriptors for the two canonical Phase-1
witnesses:

- `handoff/phase1/witnesses/upload-source-bundle-v1.tsv`
- `handoff/phase1/witnesses/steve-source-bundle-v1.tsv`

A witness descriptor carries the exact Grammar-v1 revision, selected program
root, stable source-unit/declaration lineage, repository-relative source path
plus exact SHA-256, and instance/process lineage records. Source text is not
flattened or re-encoded into the descriptor: the materializer verifies and
reads the exact checked-in `.phil` bytes, then constructs the ordinary public
`PortableSourceBundle`.

The permanent INT-007 gate independently decodes those descriptors, verifies
every referenced source digest, materializes both bundles, and runs
`resolveSourceBundleLineage`. Upload must recover
`decl:upload.client`, `decl:upload.server`, and `inst:phase1.upload`;
Steve must recover `decl:steve.put`, `decl:steve.get`, and
`inst:phase1.steve`. Neither descriptor may invent process lineage.
Traversal paths, source-byte drift, incompatible grammar revisions, and
duplicate source-unit identities fail closed.

These descriptors are governed by INT-001's ordinary-program witness boundary
and SURF-010's persisted-lineage authority. They contain no Haskell constructor
or in-memory fixture state.

## Checked semantic and ArchitectureInstance summaries

The next slice reconstructs the ordinary checked source products from the two
persisted witness SourceBundles and records an implementation-independent,
content-addressed summary for each witness:

- `handoff/phase1/witnesses/upload-checked-architecture-v1.tsv`
- `handoff/phase1/witnesses/steve-checked-architecture-v1.tsv`

For every checked declaration, the summary records the stable
`DeclarationKey` plus SHA-256 identities of:

- the exact canonical interface semantic form;
- the exact canonical definition semantic form;
- the exact `InterfaceRevision` text; and
- the exact `DefinitionRevision` text.

The architecture row records the selected program root and declaration, the
exact persisted `InstanceKey`, and the SHA-256 identity of the exact
`InstanceRevision`. These are content addresses of the semantic outputs, not
Haskell `Show` encodings or constructor names.

The permanent replay starts from the persisted witness descriptor, verifies and
loads the exact source bytes, runs the ordinary parser/checker and
`buildCheckedSourceArchitecture`, derives the summary through the production
semantic projection, and requires exact equality with the checked-in portable
summary. Another implementation can reproduce the same comparison from the
documented canonical semantic/revision rules without importing Haskell object
state.

## Deliberate remaining INT-007 work

This slice does not yet materialize or enumerate the full freeze set. Subsequent
INT-007 slices must add, and independently reconstruct/replay from portable
bytes:

- final VerificationBundles and obligation graphs;
- accepted evidence/certificates plus policy/disposition inputs;
- ArchitectureRealization, Systems, StageContract, lowering, and cost artifacts;
- final per-witness AssuranceManifests and residual TCB;
- the complete positive/negative conformance corpus with stable fixture IDs,
  expected competent layers, and exact Matrix/Certified governing authority.

The full INT-007 exit condition is reached only when a clean consumer can start
from the handoff manifest and reconstruct/replay the advertised freeze without
first-implementation-private fixture state.
