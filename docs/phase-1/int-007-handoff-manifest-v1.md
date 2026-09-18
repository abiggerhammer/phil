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

The permanent gate also requires a bijection with this initial inventory, so a
row cannot silently disappear or an unreviewed row silently appear while this
slice is the active handoff spine.

## Deliberate remaining INT-007 work

This slice does not yet materialize or enumerate the full freeze set. Subsequent
INT-007 slices must add, and independently reconstruct/replay from portable
bytes:

- framed-upload and Steve persisted SourceBundles and selected roots;
- checked declaration/semantic and ArchitectureInstance outputs, or exact
  independently reconstructible equivalents;
- final VerificationBundles and obligation graphs;
- accepted evidence/certificates plus policy/disposition inputs;
- ArchitectureRealization, Systems, StageContract, lowering, and cost artifacts;
- final per-witness AssuranceManifests and residual TCB;
- the complete positive/negative conformance corpus with stable fixture IDs,
  expected competent layers, and exact Matrix/Certified governing authority.

The full INT-007 exit condition is reached only when a clean consumer can start
from the handoff manifest and reconstruct/replay the advertised freeze without
first-implementation-private fixture state.
