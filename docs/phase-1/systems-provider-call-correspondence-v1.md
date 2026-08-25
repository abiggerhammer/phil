# Phase 1 Systems provider-call correspondence v1

Status: bounded executable conformance slice for `SYS-005`.

## Governing rule

A Systems provider call is valid because it is linked to the exact selected provider admission and the exact semantic operation correspondence accepted for that provider selection.

It is **not** valid merely because:

- a runtime symbol has the expected spelling;
- an ABI signature looks compatible;
- a backend function happens to be callable;
- two providers expose similar operation names; or
- the selected provider satisfies the same public interface as some other provider.

The StageContract relation therefore keeps provider selection, admission identity, semantic operation identity, implementation-entry identity, and runtime symbol/signature metadata distinct.

## Selected provider registry

`SelectedProviderAdmission` records one provider already accepted by the qualification/admission layer and selected for the current realization:

- exact provider occurrence;
- exact required `InterfaceRevision`;
- exact provider qualification subject;
- exact checked `QualificationAdmissionRevision` and admission decision;
- exact public `ProviderOperationKey` to qualified implementation-entry correspondence; and
- runtime symbol metadata retained for inspection.

SYS-005 consumes this accepted selection. It does not rerun PROV-001 through PROV-016 at every Systems call site.

A rejected provider admission cannot justify a Systems call.

## Provider call links

Every declared Systems provider-call mechanism receives one `ProviderCallLink`.

The accepted binding form carries:

```text
provider occurrence
qualification admission revision
required interface revision
semantic provider operation
qualified implementation entry
```

The checker requires all five facts to match the selected provider registry exactly.

The link also carries runtime symbol and signature metadata. Those fields are inspectable but do not establish semantic correspondence.

`RuntimeSymbolOnlyProviderCall` is an explicitly represented rejected form. It exists so the StageContract verifier can diagnose the exact invalid inference rather than treating symbol similarity as an implicit mapping rule.

## Matching symbol, wrong admission

A call can retain the exact same runtime symbol and signature while citing a different provider admission. The call is rejected.

This is important for implementation replacement and multi-provider programs: contract or ABI resemblance does not transfer qualification lineage.

## Right admission, wrong operation

An exact provider admission is still insufficient when the call names an operation not present in that admission's checked operation correspondence.

Likewise, the implementation entry must be the exact entry already associated with that semantic operation. An implementation symbol or entry for another operation cannot be substituted merely because the machine signature looks compatible.

## Runtime symbol rename

Changing only runtime symbol metadata does not invalidate an otherwise exact semantic provider-call binding in this bounded checker.

This does not claim that all target profiles consider symbols non-identity-bearing. A later ABI/profile layer may make a symbol or linkage fact part of target artifact identity. The SYS-005 rule is narrower: symbol identity cannot *create or repair* semantic provider correspondence.

## Framed-upload migration bridge

The Phase-0 framed-upload witness predates the Phase-1 provider model. Its storage operation is already represented by an exact `StorageBoundary`, exact storage-success obligation revision, and exact runtime assurance evidence.

For SYS-005 the witness therefore uses a deliberately narrow collapsed-opaque provider admission bridge:

- provider interface: `upload.provider.storage.v1`;
- provider occurrence: `upload.storage-provider`;
- opaque subject: the exact Phase-0 storage runtime boundary;
- semantic operation: `upload.store`;
- implementation entry: `phase0.runtime.store`;
- evidence: `evidence.upload.storage.runtime`; and
- validity: the existing Phase-0 storage-success boundary only.

This bridge does **not** claim that Phase 0 had Phase-1 provider-wide state, lifecycle, authority, replacement, or evidence-competence semantics. It is only an exact admission descriptor for the operation whose assurance already exists, allowing the required legacy witness to participate in the same SYS-005 StageContract relation as Steve.

## Steve

Steve's selected provider registry is derived mechanically from the real PROV-016 artifacts:

- `DigestProvider[SHA256]` admission and its `digest.compute` / `digest.check` correspondences;
- `BlobProvider` admission and its `blob.read` / `blob.install-if-absent` correspondences.

The Systems call links then bind:

```text
StevePut / DigestProvider.compute
StevePut / BlobProvider.install-if-absent
SteveGet / BlobProvider.read
SteveGet / DigestProvider.check
```

to those exact provider selections and checked implementation entries.

## Conformance corpus

The SYS-005 corpus requires:

1. framed upload acceptance through its exact opaque storage admission bridge;
2. Steve acceptance through its real PROV-016 provider selections;
3. rejection of a matching runtime symbol paired with the wrong admission revision;
4. rejection of runtime-symbol/signature-only mapping;
5. rejection of the wrong semantic operation while the runtime symbol remains unchanged;
6. rejection of the wrong qualified implementation entry;
7. rejection of the wrong provider interface;
8. acceptance of a harmless runtime-symbol rename when the exact semantic binding remains unchanged;
9. rejection when one declared provider-call site lacks a call link;
10. rejection of an unknown provider occurrence;
11. rejection when the selected provider admission itself is rejected; and
12. deterministic provider-call StageContract identity under map reordering.

## Deferred

This slice does not yet establish:

- runtime authority/effect correspondence (`SYS-006`);
- branch-sensitive resource/failure preservation (`SYS-007`);
- protocol or boundary lowering relations;
- evidence-copy/subject-transfer correspondence;
- runtime assurance-site/carrier coverage;
- erasure and target-strengthening rules;
- deployment/next-stage requirements; or
- certified cost attribution.

Those remain later compositional StageContract relations over the same base stage and exact provider-call lineage.
