# Steve 0 provisional assurance manifest

This directory documents the branch-only Steve 0 assurance witness exercised by `test/SteveAssuranceMain.hs`.

The executable witness uses the public `Phil.Assurance` API and `verifyManifest`; it does not add Steve-specific rules to the Phil checker. Its target is deliberately `steve0-semantic` with compilation profile `semantic/provisional`. The build identity strings and lowering-ledger root are semantic placeholders, not claims that a native Steve implementation or frozen serialized manifest already exists.

## Certification scope

All twelve Steve 0 obligations from the Drive obligation matrix are selected into the certification scope:

| Obligation | Closure in the provisional manifest |
| --- | --- |
| `STEVE-PUT-DIGEST` | kernel checks successful-result evidence + runtime digest production |
| `STEVE-GET-DIGEST` | kernel checks successful-result evidence + runtime digest validation |
| `STEVE-NO-CLOBBER` | restricted authority surface + BlobProvider assumption boundary |
| `STEVE-ATOMIC-PUBLISH` | BlobProvider assumption boundary |
| `STEVE-PUT-IDEMPOTENT` | kernel-derived from put digest, no-clobber, and byte-equality obligations |
| `STEVE-COLLISION-FAILS` | fail-closed control + runtime existing-object digest check after byte inequality |
| `STEVE-CORRUPTION-FAILS` | fail-closed control + runtime digest validation |
| `STEVE-NO-DELETE` | restricted public/provider authority surface |
| `STEVE-CRASH-STATE` | BlobProvider assumption boundary, depending on atomic publication |
| `STEVE-INSTALL-BORROW-SCOPE` | Phil shared-loan check + BlobProvider copied-publication assumption |
| `STEVE-DIGEST-EVIDENCE-IDENTITY` | stable-identity evidence contract + DigestProvider assumption boundary |
| `STEVE-BYTE-EQUALITY-EVIDENCE` | branch-evidence checking + retained exact byte comparison |

There are no exports in the provisional manifest.

## Assumption nodes

Three first-class assumptions are selected:

1. `assumption.steve.digest_provider_contract` — initial TCB boundary for faithful SHA-256 computation and stable-identity evidence production.
2. `assumption.steve.blob_provider_contract` — initial TCB boundary for read, atomic no-replace publication, crash visibility, and copying before a shared loan ends.
3. `assumption.steve.sha256_collision_resistance` — practical global-identity assumption only.

The third assumption is intentionally **not** a dependency of the twelve safety obligations. The executable test removes it, recomputes the manifest identity, and requires the safety manifest to remain valid. This encodes the Steve design rule that observed collisions fail closed without assuming SHA-256 injectivity or collision impossibility.

Conversely, removing either provider assumption must make verification fail because current Steve obligations still rely on those declared TCB boundaries.

## Retained runtime assurance

The provisional manifest records three runtime-cost identities:

- `steve.runtime.digest_compute`
- `steve.runtime.digest_check`
- `steve.runtime.bytes_compare`

Five `RetainedRuntimeUse` nodes bind those costs to the put digest, get digest, collision classification, corruption detection, and exact-byte-comparison obligations. This is the first Steve application of ADR-011's distinction between proof that can disappear and uncertainty that remains as runtime work.

## What this proves today

A green Steve assurance-witness step in the branch-only **Steve Branch** workflow means the Steve design can be represented as a closed, internally consistent graph accepted by the current assurance-manifest verifier, including assumption selection, obligation dependencies, runtime mechanisms, cost references, stable IDs/digests, and manifest identity.

It does **not** mean the `.phil` Steve witness has passed whole-component semantic checking, the filesystem provider is implemented, the provider assumptions are discharged, or the runtime cost references have concrete lowering measurements yet. Those are later promotion points.
