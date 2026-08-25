# Phase 1 Systems authority/effect correspondence v1

Status: bounded executable conformance slice for `SYS-006`.

## Governing rule

A Systems provider call may not gain semantic authority or source-observable effects merely because the selected implementation can perform them.

For every provider call already bound by SYS-005, the StageContract relation records and checks:

- the exact selected provider occurrence and operation;
- the operation's qualified public semantic effect bound;
- the provider's admitted public authority surface;
- an explicit operation-local assignment of public authority;
- any explicitly qualified provider-internal authority assigned to that operation;
- the effects actually attributed to the Systems call; and
- the authority actually exercised by that Systems call.

Effect permission and authority remain separate.

## Qualified provider surfaces

For a normal Phase-1 qualified provider, the public operation effect bound is derived from the **expected/public** side of the checked callable refinement stored in `CheckedProviderSemanticQualification`.

The StageContract does not supply a second free-form copy of that bound.

Provider authority is provider-wide in PROV-009/AUTH-006, so SYS-006 adds a separate explicit operation-to-authority assignment. The assignment is checked against `CheckedProviderAuthorityQualification`:

- every assigned public grant must be in the admitted client-visible authority set;
- the union of operation-local public assignments must account for the client-visible provider surface in this bounded slice;
- an internal grant may be assigned only when it is one of the checked extra internal grants; and
- its exact qualification disposition must match.

This prevents a provider operation from borrowing another operation's public authority merely because both belong to the same provider.

## Opaque migration surfaces

The framed-upload witness predates the Phase-1 provider model. Its Phase-0 storage boundary is therefore represented by an explicit opaque provider surface grounded in `evidence.upload.storage.runtime`.

The bridge gives only the already-bounded `upload.store` operation:

- semantic effect `upload.store`; and
- exact storage `store` authority.

An opaque operation surface without an exact evidence reference is rejected. The bridge does not retroactively grant the richer Phase-1 provider model to Phase 0.

## Effect widening

Each concrete Systems effect use records:

- the semantic effect;
- whether it is source-observable or internal realization work; and
- an optional realization-refinement revision.

The rules are:

1. an effect already inside the qualified public may-effect bound is accepted;
2. a source-observable effect outside that bound is rejected, even if a target refinement is named;
3. an internal-only target effect outside the source bound is accepted only with a nonempty explicit realization-refinement revision; and
4. an internal target effect outside the bound with no refinement is rejected.

This is the bounded SYS-006 form of the broader rule:

> Target realization may add machinery; it may not silently add source semantics.

The more detailed authority/failure/subject-transfer/cost accounting for specific inserted staging operations remains the later SYS-017 pressure case.

## Authority exercise

A Systems call may exercise public provider authority only when that exact grant is assigned to the exact semantic provider operation.

Provider-internal authority is not ambiently inherited by every call. To exercise an internal grant at Systems level, the operation-local StageContract relation must assign that exact grant and exact checked provider qualification disposition.

Thus:

- `BlobProvider.read` receives read authority;
- `BlobProvider.install-if-absent` receives install-if-absent authority;
- DigestProvider receives no storage authority;
- overwrite/delete grants retained inside the BlobProvider implementation do not become client-call authority merely because the provider possesses them.

## Witnesses

### Steve

The Steve SYS-006 witness derives its semantic surfaces from the real PROV-016 provider artifacts:

- DigestProvider `compute` / `check` effect bounds come from their checked public callable contracts and carry no authority;
- BlobProvider `read` carries only the read effect and read authority;
- BlobProvider `install-if-absent` carries only the install effect and install authority; and
- broader overwrite/delete authority remains inside the provider qualification boundary unless separately assigned with its exact disposition.

### Framed upload

The Phase-0 storage call is represented as one opaque, evidence-grounded `upload.store` surface and one exact Systems use.

Both witnesses pass the same SYS-006 verifier layer above SYS-005.

## Conformance corpus

The dedicated corpus covers:

1. framed-upload acceptance;
2. Steve acceptance;
3. rejection of a source-observable effect outside the semantic bound;
4. acceptance of an internal target effect outside the source bound with an exact realization-refinement revision;
5. rejection of the same internal effect without refinement;
6. rejection when one provider operation tries to exercise another operation's public authority;
7. rejection of a provider-internal grant that is qualified provider-wide but not assigned to the exact operation;
8. rejection when the StageContract surface itself widens admitted public authority;
9. rejection of an opaque provider surface with no grounding evidence; and
10. deterministic authority/effect stage identity under map reordering.

## Boundaries

This slice does not yet establish:

- branch-sensitive resource/failure preservation (`SYS-007`);
- loop/backedge and closure-capture preservation (`SYS-008`);
- protocol or boundary realization (`SYS-009`/`SYS-010`);
- evidence copy/subject transfer (`SYS-011`);
- erasure, assumption, or strengthening closure (`SYS-012`--`SYS-014`);
- runtime-site/carrier many-to-many relations (`SYS-015+`);
- full staging-copy authority/failure/subject-transfer/cost accounting (`SYS-017`); or
- a Rocq theorem for SYS-006.

Those remain separate relation layers over the same generic StageContract envelope.
