# Steve rejected-program corpus

These files are intentionally parser-valid Phil surface programs that must eventually fail semantic checking for a stated Steve/Phil reason. Until the general Steve checker environment exists, CI asserts only that they remain syntactically valid witnesses.

| File | Intended rejection | Why |
| --- | --- | --- |
| `01-return-unverified-bytes.phil` | Missing evidence / result contract | `GetOk` transfers bytes without `DigestMatches`. |
| `02-prove-opaque-digest.phil` | Opaque proof | `DigestMatches` cannot be manufactured by generic `prove`. |
| `03-drop-owned-read-result.phil` | Linear completion | The `found(bytes)` arm drops its `OwnedBytes`. |
| `04-duplicate-owned-result.phil` | Structural use | One linear byte owner is transferred twice. |
| `05-collision-as-success.phil` | Result/obligation contract | The program observes unequal bytes that both match one `ContentId` and nevertheless returns `PutOk`. |
| `06-integrity-as-not-found.phil` | Typed failure/result contract | Detected integrity failure is hidden as absence. |
| `07-borrow-indexed-digest-evidence.phil` | Borrow escape / invalid evidence contract | Persistent digest evidence is indexed by an ephemeral loan instead of the stable byte-object identity. |

The rejection labels are design targets, not claims about the current upload-specialized checker. As generic result shapes, declared evidence producers, and architecture/static-signature checking land, each fixture should gain an executable expected-rejection assertion.
