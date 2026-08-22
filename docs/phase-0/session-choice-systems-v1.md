# Phase 0 Systems session-choice representation v1

Status: implementation candidate

This slice corrects a Systems-layer information loss in the final client response. Phil Core already represents session branches as a semantic label, optional payload binder/type, and continuation. The historical Phase 0 Systems graph collapsed the final external choice to an anonymous runtime Boolean and therefore lost both branch payloads.

The historical Phase 0 and already-certified server/runtime artifacts are not mutated in place; this is a successor Systems candidate derived from the merged rejected-response/storage lineage.

## Systems commitment

Systems represents session choice by semantic labels, branch-local payload identity, and continuation control flow. Discriminator representation and payload layout are target decisions.

The new terminator is conceptually:

```text
TermSessionOffer transport {
  label -> (optional branch-local payload binding, target block)
}
```

Labels are stored in a canonical map, so source enumeration order is not semantic identity.

A payload binding is defined on its branch edge and becomes live at the target block. In this Phase 0 representation, every payload-bearing target must be a dedicated binder block whose sole predecessor is the corresponding offer block. A branch-local payload may not be used from another arm. General cross-branch joins/phi-like payload transport remain a future explicit representation problem rather than an implicit escape hatch.

## Final-response witness

The corrected client boundary is:

```text
client.payload:
  select payload
  send_exact payload
  offer on client.transport {
    accepted -> bind client.upload_id : UploadId -> client.accepted
    rejected -> bind client.digest_failure : DigestFailure -> client.rejected
  }

client.accepted:
  record_upload_id(client.upload_id)
  end success

client.rejected:
  end failure
```

The old `client.result_branch : Bool` and generic `receive accepted/rejected label` operation are absent from this candidate.

The `DigestFailure` binding is retained even though the current client does not inspect it. Any later target may erase its runtime representation only after establishing that the value has no observable use in the exact program/profile.

## Backend competence boundary

This slice deliberately does not choose a physical final-response decoder, numeric discriminator, switch layout, wire buffering strategy, or UploadId client representation. Existing LLVM lowerers therefore fail closed on `TermSessionOffer` rather than silently recreating the old Boolean approximation. A later target slice must explicitly lower this terminator and validate the label/payload/continuation relation.

## Follow-on normalization

The final response is the first concrete use. The same representation can later replace the earlier payload-erasing incoming choices (`version(selected)`, `reject(reason)`, and other branch payloads). Outgoing `select` operations remain represented by the historical generic runtime call in this slice; a later normalization can introduce the dual explicit Systems select operation without disturbing the current accepted/rejected proof harvest.
