# Phase 1 Systems branch resource/failure correspondence v1

Status: bounded executable conformance slice for `SYS-007`.

## Governing rule

Every represented source outcome at a branch-sensitive Systems site must preserve its exact resource/failure semantics on the corresponding target arm.

A target arm may not:

- omit a live restricted owner from accounting;
- claim an owner was released when no release/cleanup occurred;
- retain an owner after the target arm actually released it;
- treat a scoped borrowed view as the owning resource;
- turn a source-fatal outcome into a continuing path; or
- silently reinterpret a continuing owner as an unaccounted terminal residue.

The checker consumes the generic SYS-001--006 stage stack first. It then binds one exact source outcome contract to one exact Systems branch/choice terminator.

## Branch site contract

A `BranchSiteContract` records:

- exact Systems mechanism key;
- exact function and block;
- exact tracked owning `ValueId` set; and
- one `BranchOutcomeContract` for every concrete outgoing arm of that terminator.

The checker independently derives the target arm domain from the Systems terminator. Supported bounded branch forms are:

- boolean branch;
- recognition success/failure;
- runtime check success/failure;
- exact receive success/failure;
- exact send success/failure;
- storage success/failure;
- session offer labels; and
- runtime choice labels.

Missing or invented outcomes reject.

## Owner fate

For every tracked owner, every outcome has exactly one fate:

- `OwnerContinues` — the owner is not released on the target arm and the arm remains continuing;
- `OwnerReleased` — exactly one release/cleanup/destruction operation occurs for the owner on the target arm; or
- `OwnerReturnedAtTerminal` — the owner is preserved through a normal terminal boundary rather than destroyed locally.

The owner-fate map must have exactly the same domain as the tracked-owner set. This is the bounded SYS-007 no-loss rule.

The checker counts explicit target-arm destruction from:

- `OpReleaseOwner`;
- `OpCleanupPartial`; and
- `OpDestroyPending`.

More than one destructive operation for the same tracked owner is an explicit double-release error.

A `BorrowedSlice` is not an owning residue and cannot be placed in the tracked-owner domain.

## Failure/control class

Each source outcome also declares one exact control class:

- continuing;
- normal terminal with exact reason; or
- fatal terminal with exact reason.

The target arm's actual terminator must match exactly. A source fatal outcome therefore cannot acquire a fabricated continuation merely because the target CFG has an otherwise type-correct edge.

Terminal arms do not contribute a continuing join state; they still owe complete resource accounting. This follows the Resource State, Join, and Invariant Checking Contract and ADR-005.

## Witness pressure

### Framed upload

The bounded upload witness checks two real resource-sensitive sites from the mature Phase-0 Systems graph:

1. exact payload receive:
   - success preserves `server.payload` and continues to digest checking;
   - early EOF cleans up `server.payload` exactly once and ends fatally as `EarlyEOF`.
2. digest check:
   - success preserves `server.payload` and continues to storage;
   - digest mismatch releases `server.payload` exactly once and ends normally with failure.

### Steve

The bounded Steve witness checks the provider paths whose current Systems graph already exposes precise owner behavior:

1. `DigestProvider.compute` preserves the unique candidate owner while operating through its borrowed view;
2. every `BlobProvider.install-if-absent` outcome preserves the candidate owner to the terminal caller boundary because the provider qualification says the candidate is borrowed, not consumed.

The checker therefore treats the candidate owner and its scoped digest/install views as different resource roles.

## Conformance corpus

The dedicated corpus requires:

- upload and Steve acceptance;
- rejection of missing reachable outcomes;
- rejection of missing owner-fate entries;
- rejection of an invented release;
- rejection when a target-released owner is relabeled as a terminal return;
- rejection of fatal-to-continuing control laundering;
- rejection of an implicit continuing owner on a terminal arm;
- rejection of a borrowed view used as the owner;
- mandatory semantic outcome identity;
- exact branch mechanism identity; and
- deterministic stage identity under map reordering.

## Deferred to later SYS slices

This slice does not yet implement the general join/loop state telescope (`SYS-008`), protocol endpoint succession (`SYS-009`), exact boundary send/receive commit semantics (`SYS-010`), evidence subject transfer (`SYS-011`), erasure/strengthening, or full path-sensitive resource interpretation across arbitrary multi-block target regions.

The v1 checker deliberately checks the first target block of each exact outcome arm. General resource-carrying reconvergence and backedge projection belong to the shared JoinContract work in SYS-008 rather than being duplicated here.
