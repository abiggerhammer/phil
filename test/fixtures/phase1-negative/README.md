# Phase 1 portable negative corpus

This directory carries the INT-004 migration from implementation-private negative tests to portable conformance fixtures.

`manifest.tsv` is normative for the migrated frozen Phase-0 semantic negatives. Each row gives a stable fixture identity, portable `.phil` input path, implementation-independent rejection class label, earliest competent rejection layer, explicit environment profile name, and governing Matrix authority.

`environment-profiles-v1.tsv` is the portable representation of the currently migrated checker environments. Its fields are semantic data rather than Haskell constructor text or fixture filenames:

- `profile_id` — stable profile identity referenced by `manifest.tsv`;
- `binding_name` / `binding_mode` — the initial architecture-supplied binding;
- `session_kind` — currently `receive` or `offer`;
- `message_name` / `message_type` / `terminal_outcome` — receive-session data; `message_type` supports `opaque:<name>` and `frame:<grammar>`;
- `branches` — semicolon-separated `label:terminal-outcome` entries for offer sessions;
- `primitive_bindings` — semicolon-separated `source-name:semantic-operation` entries;
- `legacy_receive_frame_raw` — explicit semantic compatibility flag for the old raw-frame receive boundary.

A literal `-` means the field is not applicable to that session shape. Version 1 deliberately starts with a small semantic vocabulary and currently materializes `phase0.simple-receive`, `phase0.wrong-order`, `phase0.nonexhaustive-offer`, `phase0.legacy-raw`, and `phase0.failure-reuse`. These cover frozen fixtures P1-NEG-P0-001 through P1-NEG-P0-005 plus P1-NEG-P0-009. The rows contain no `.phil` path or Haskell implementation identity; another checker can reconstruct the same competent-layer context from the table alone.

The remaining profiles still pass through the transitional Phase-0 compatibility adapter until their richer recognition/proof/policy environments are encoded in later INT-004 slices. Materialized profiles are forbidden from falling back to that adapter, so deletion or corruption of portable environment material fails closed.

The manifest, not the legacy filename table, owns expected rejection classes. Legacy classification parity remains a migration regression only. Exact diagnostic strings and Haskell exception constructors are not conformance authority; the portable class labels are semantic labels that implementations map to their own diagnostics.
