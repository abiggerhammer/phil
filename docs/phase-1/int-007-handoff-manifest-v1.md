# INT-007 Phase-1 handoff manifest v1 — integrity spine

Matrix case **INT-007** requires the Phase-1 freeze to publish one versioned,
machine-readable handoff manifest whose artifacts can be consumed without
Haskell-private object state. The manifest is now the integrity spine for the
completed INT-007 freeze: every admitted portable handoff artifact and the
complete conformance freeze are content-addressed from this root.

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

## VerificationBundle and obligation-graph handoff

The next layer reconstructs each witness's canonical Phase-1
`VerificationBundle` from the persisted source handoff through the same INT-002
verification path used by manifest closure. The portable verification summary
records:

- exact SHA-256 identities for the VerificationBundle, source revision,
  architecture projection, and obligation graph;
- the exact selected assurance-policy revision;
- every obligation RevisionId plus its statement digest;
- every obligation dependency edge;
- every certification-scope RevisionId; and
- every accepted evidence entry ID, evidence digest, and target obligation
  RevisionId.

The graph root is therefore not the only handoff fact: an independent consumer
can reconstruct the complete node/edge/scope domain and check that the canonical
graph and bundle revisions agree. Haskell container order and constructors are
not part of this representation.

The first VerificationBundle handoff pair is:

- `handoff/phase1/witnesses/upload-verification-bundle-v1.tsv`
- `handoff/phase1/witnesses/steve-verification-bundle-v1.tsv`

Both are governed by INT-002 and VER-012 and are content-addressed from the
top-level handoff manifest.

The progressive Ping corpus now carries five distinct VerificationBundles for
the accepted source programs governed by INT-008/INT-009: one-shot Ping,
request/reply with explicit output, bounded Ping, productive unbounded Ping, and
interruptible Ping with explicit cancellation. The conventional host-SIGINT
termination of the unbounded program is a runtime realization of the same source
and does not require a second source VerificationBundle.

The whole-source bridge checks each exact persisted Grammar-v1 source, requires
its program root to instantiate the checked architecture, derives the program
architecture occurrence through the normal ArchitectureInstance identity
machinery, content-binds the exact source bytes and stable architecture/program
lineage, and constructs the canonical VerificationBundle. Ping currently has no
assurance-ledger residual obligations or accepted evidence entries, so these five
bundles deliberately carry the canonical empty obligation graph rather than
inventing assurance facts from runtime/conformance tests.

The five bundle summaries are content-addressed from the top-level handoff
manifest under INT-008/INT-009 and VER-012.

## Accepted assurance inputs and closure policy

The next layer persists the exact assurance inputs selected behind the canonical
Upload and Steve VerificationBundles:

- `handoff/phase1/witnesses/upload-assurance-inputs-v1.tsv`
- `handoff/phase1/witnesses/steve-assurance-inputs-v1.tsv`

Each portable file records the exact application-assurance policy revision,
permitted closure dispositions, the disposition set actually required by the
selected inputs, and the selected accepted `EvidenceEntry`, `Assumption`,
`ExportEntry`, and `AssuranceUse` records. Evidence rows preserve exact
obligation revision, assurance kind and role, input digests, assumption and
evidence/obligation dependencies, validity-scope dimensions, justification
identities, runtime mechanism/residue/cost identities, and optional evidence or
runtime artifact identity.

The decoder reconstructs those assurance records and recomputes their canonical
digests using the ordinary assurance identity functions. It rejects digest drift,
missing selected dependencies, unused selected assumptions, malformed portable
text, and any required disposition not permitted by the persisted policy. The
disposition mapping itself is shared with `ManifestClosure`; the handoff does
not carry a second policy interpretation.

The permanent replay also reconstructs each corresponding VerificationBundle and
requires every accepted-evidence reference to match the portable selected ledger
by exact evidence ID, evidence digest, and obligation revision.

The current Upload and Steve accepted evidence has no external evidence/certificate
artifact body: its `evidenceArtifact` and runtime implementation artifact fields
are absent. The format preserves artifact ref/digest identity when present, but
INT-007 does not invent certificate files that are not inputs to these bundles.
Any future referenced artifact body must additionally be content-addressed as its
own top-level `evidence` or `certificate` handoff artifact.

Both assurance-input files are governed by INT-002 and VER-012 and are
content-addressed from the top-level handoff manifest.

## Runtime/build handoff

The Upload and Steve freeze now includes five portable runtime/build artifacts
per witness:

- ArchitectureRealization;
- Systems artifact;
- final StageContract closure;
- lowering ledger; and
- cost attribution.

The permanent replay derives these artifacts from the ordinary StageClosure
witnesses and requires exact equality with the checked-in canonical bytes. The
top-level manifest binds each artifact under its governing VER/SYS Matrix
authority rather than treating INT-007 itself as semantic authority.

## Final assurance closure and residual TCB

The final Upload and Steve `AssuranceManifest` values are persisted as portable
handoff files and reconstructed against the exact selected assurance ledgers.
Their identities are recomputed with the ordinary `deriveManifestId` logic and
the manifests are replayed through the ordinary assurance verifier.

Each witness also carries a residual-TCB handoff derived from its certified
release. The TCB records the exact final manifest identity, release-profile
revision, required trust-kind domain, and every named trust boundary with its
kind, name, revision, and basis. The boundary-kind domain must equal the
release profile's declared trust domain exactly.

All four files are content-addressed from the top-level handoff manifest.

## Complete conformance freeze

`handoff/phase1/conformance-freeze-v1.tsv` is the content-addressed conformance
inventory for the Phase-1 freeze.

It carries all **145 stable conformance cases** currently in scope:

- 28 accepted Grammar-v1 parser fixtures governed by SURF-002;
- 36 syntax-negative Grammar-v1 fixtures governed by SURF-003; and
- 81 portable semantic-negative cases governed by their existing exact
  Matrix/Certified authorities.

For every case the freeze records a stable ID, the portable fixture carrier,
its exact SHA-256, expected acceptance/rejection, earliest competent layer, and
governing authority.

The semantic-negative corpus has two legitimate carrier forms. The original 20
cases are repository-level `.phil` files under `examples/rejected/`. The newer
61 cases are stable rows in eight subordinate portable manifests; their manifest
bytes and all auxiliary TSVs used to materialize and replay those cases are
content-bound as support entries under certified
`PHIL-P1-CONFORMANCE-001`.

The generator requires exactly nine semantic-negative manifests and exactly 81
unique semantic-negative fixture IDs, preserves the surface manifest/file
bijection, rejects duplicate fixture identities, and rejects use of INT-004 as
fixture semantic authority.

## INT-007 exit condition

The permanent handoff workflow now checks all of the following from a clean
checkout:

1. the top-level handoff manifest has exactly the admitted freeze inventory and
   every referenced artifact matches its exact SHA-256;
2. the complete conformance freeze regenerates byte-for-byte;
3. the completed top-level handoff manifest regenerates byte-for-byte from the
   frozen artifacts;
4. Upload and Steve source, checked architecture, VerificationBundle, assurance
   inputs, runtime/build artifacts, final AssuranceManifests, and residual TCB
   reconstruct through the ordinary production paths; and
5. the dedicated surface and portable-negative conformance workflows continue
   to replay the frozen fixture corpora.

That is the INT-007 Phase-1 freeze boundary: a clean consumer can begin with the
handoff manifest and reconstruct/replay the advertised freeze without requiring
first-implementation-private fixture state.
