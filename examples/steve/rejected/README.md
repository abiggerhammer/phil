# Steve rejected-program corpus

These files are intentionally parser-valid Phil surface programs that must eventually fail semantic checking for a stated Steve/Phil reason. Until the general Steve checker environment exists, CI asserts only that they remain syntactically valid witnesses.

| File | Intended rejection | Why | Existing checker machinery | Remaining Steve wiring |
| --- | --- | --- | --- | --- |
| `01-return-unverified-bytes.phil` | Missing evidence / result contract | `GetOk` transfers bytes without `DigestMatches`. | Exact evidence matching and `MissingEvidence` rejection already exist. | Declare Steve's `DigestMatches(ContentId, ByteObjectId)` producer/requirement and general ownership-bearing result contracts. |
| `02-prove-opaque-digest.phil` | Opaque proof | `DigestMatches` cannot be manufactured by generic `prove`. | `OpaqueProof` is already executable in the Phase 0 checker and exercised by upload fixture 18. The witness now needs no Steve primitive or type alias before reaching `prove`. | Supply one opaque `DigestMatches(SortOpaque "ContentId[SHA256]", SortStableId "OwnedBytes")` declaration through the general architecture/static-environment hook. See `../architecture/opaque-proof-promotion.md`. |
| `03-drop-owned-read-result.phil` | Linear completion | The `found(bytes)` arm drops its `OwnedBytes`. | Linear completion checking is already executable. `PHIL-SURFACE-SCOPE-001` now formally proves that successful scope exit cannot leave a branch-local linear binding live. | Give `blob_read` a generic result shape whose `found` arm introduces a linear `OwnedBytes` owner. |
| `04-duplicate-owned-result.phil` | Structural use | One linear byte owner is transferred twice. | Linear/affine use-after-consumption rejection is executable. `PHIL-SURFACE-FRESH-001` now formally proves the successor/rebind bridge has no intermediate duplicate owner and requires a fresh final name. | General result constructors must transfer ownership rather than collapse constructed results to opaque unrestricted scalars. |
| `05-collision-as-success.phil` | Result/obligation contract | The program observes unequal bytes that both match one `ContentId` and nevertheless returns `PutOk`. | Exact evidence identity and branch-sensitive checking exist. | Declare evidence-bearing `bytes_compare` results plus the Steve success obligation/result contract that forbids success after witnessed inequality plus two matching digests. |
| `06-integrity-as-not-found.phil` | Typed failure/result contract | Detected integrity failure is hidden as absence. | Branch-sensitive terminal/result checking exists in the generic surface checker. | Declare Steve result variants and the operation contract distinguishing `GetIntegrityFailure` from `GetNotFound`. |
| `07-borrow-indexed-digest-evidence.phil` | Borrow escape / invalid evidence contract | Persistent digest evidence is indexed by an ephemeral loan instead of the stable byte-object identity. | Shared-loan scope and `BorrowEscape` are executable; stable identities in propositions are already part of Phil's accepted semantics. | Generalize evidence-producer contracts so the checker can require a stable owner/snapshot identity and reject a proof whose proposition names the ephemeral view token. |

## Latest main sync: surface scope and fresh ownership proofs

The branch is synchronized through main commit `4b5e68c5` (PR #25). That upstream slice is proof-only apart from proof-project/CI wiring: it adds `proof/Phil/Surface/ScopeJoin.v` and `proof/Phil/Surface/FreshOwnership.v`.

The new Rocq results materially strengthen the proof story behind Steve's ownership witnesses:

- `PHIL-SURFACE-SCOPE-001` proves that a successful continuing branch cannot exit lexical scope with a branch-local linear binding still live, that local metadata is pruned, and that retained metadata agrees across continuing branches while preserving the Core linear join.
- `PHIL-SURFACE-FRESH-001` proves the surface successor bridge stages one synthetic continuation owner, consumes that temporary owner, and rebinds only to a globally fresh programmer-visible name; there is no intermediate state with two owners for the continuation.

These results improve the assurance basis for `03-drop-owned-read-result.phil` and `04-duplicate-owned-result.phil`, but they do **not** yet promote either fixture to an executable Steve semantic rejection. The upstream slice added no new Haskell declaration environment, generic `blob_read` decision shape, or ownership-bearing result-constructor machinery. A fixture should still graduate only when it reaches its intended rejection through the general checker rather than failing because a Steve type or primitive is unknown.

## First promotion is now fully specified

`02-prove-opaque-digest.phil` has been reduced to the smallest useful witness: `ContentId[SHA256]`, `OwnedBytes[0]`, and `prove DigestMatches(id, bytes.id)`. It deliberately avoids `owned_bytes_identity`, a symbolic length parameter, and every provider operation.

`../architecture/opaque-proof-promotion.md` fixes the exact one-claim static environment and the expected checker path. This means the first Steve promotion no longer needs any Steve-specific primitive semantics; it is waiting only for a general way to supply architecture/static declarations to the conformance checker.

## Promotion order

The first semantic promotions should require as little Steve-specific checker machinery as possible:

1. `02-prove-opaque-digest.phil` once the general harness can supply the one-claim Steve static environment specified in `../architecture/opaque-proof-promotion.md`.
2. `03-drop-owned-read-result.phil` once generic decision arms can introduce owning values.
3. `04-duplicate-owned-result.phil` once constructed result values preserve ownership transfer.
4. `01-return-unverified-bytes.phil` once result postconditions can require Steve evidence.
5. `06-integrity-as-not-found.phil` once result/failure distinctions are architecture-declared.
6. `05-collision-as-success.phil` once evidence-bearing byte comparison and the full put-success contract are wired.
7. `07-borrow-indexed-digest-evidence.phil` once stable-identity requirements on evidence producers are executable at the general architecture boundary.

The ordering is a readiness estimate, not a semantic priority. A fixture should graduate only when the checker rejects it for its stated reason rather than because an unrelated Steve primitive or type is unknown.
