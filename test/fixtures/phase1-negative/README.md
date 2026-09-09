# Phase 1 portable negative corpus

This directory carries the INT-004 migration from implementation-private negative tests to portable conformance fixtures.

`manifest.tsv` is normative for the migrated frozen Phase-0 semantic negatives. Each row gives a stable fixture identity, portable `.phil` input path, implementation-independent rejection class label, earliest competent rejection layer, explicit environment profile name, and governing Matrix authority.

`environment-profiles-v1.tsv` is the portable representation of profile-level checker environment data. Its fields are semantic data rather than Haskell constructor text or fixture filenames:

- `profile_id` — stable profile identity referenced by `manifest.tsv`;
- `binding_name` / `binding_mode` — the primary architecture-supplied endpoint binding, or `-` when the profile has no primary binding;
- `session_kind` — `receive`, `offer`, `select`, or `none` for a primitive-only environment;
- `message_name` / `message_type` / `terminal_outcome` — receive-session data; `message_type` supports `opaque:<name>`, `frame:<grammar>`, `bytes:nat:<n>`, and `bytes:toNat-field:<binding>.<field>:u64`;
- `branches` — semicolon-separated `label:terminal-outcome` entries for offer/select sessions;
- `primitive_bindings` — semicolon-separated `source-name:semantic-operation` entries;
- `legacy_receive_frame_raw` — explicit semantic compatibility flag for the old raw-frame receive boundary.

`environment-bindings-v1.tsv` is the normalized repeated-binding layer for profiles that need additional architecture-supplied values beyond the primary endpoint. Each row carries `profile_id`, `binding_name`, `binding_mode`, a portable `binding_type`, and `binding_shape`. The vocabulary now includes `bool`, `frame:<grammar>`, `validated:<claim>:<context>:<subject>`, and explicitly sorted opaque values, with `plain`, `record:<grammar>`, fixture-raw, and owned-bytes shapes. Duplicate binding names within one profile are invalid, and binding rows may only refer to declared portable profiles.

`environment-requirements-v1.tsv` carries competent-boundary proof requirements independently of Haskell maps. Each row names a profile, a requirement site (`receive-exact` or `select`), the site label when applicable, and a portable proposition. The initial proposition vocabulary uses explicit atoms such as `atom:BeginPolicy:var:kappa2,var:begin`.

`environment-static-claims-v1.tsv` carries the corpus-level static claim context inherited by every frozen Phase-0 checking environment. Each row gives a claim name, declaration kind, and ordered parameter list with portable sorts. The initial corpus declares `DigestMatches` as opaque with `begin : opaque Frame` and `payload_id : stable-id OwnedBytes`. This is portable semantic context, not a Haskell fixture alias; removing or corrupting it must fail closed rather than causing a fixture to reject earlier as an unknown claim.

A literal `-` means the field is not applicable to that profile shape. Version 1 currently materializes the original seed, recognition, common, and incompatible-join environments and is being extended to the validation/provenance profiles. All portable data is path-free and contains no Haskell implementation identity; another checker can reconstruct the same competent-layer context from these tables alone.

`phase0.common` is intentionally represented as a no-initial-binding profile. The affected fixtures get their resource modes from intrinsic surface types (`StoreCap`, `OwnedBytes`, `U32`) and require only explicit primitive semantics for authority exercise, cancellation allocation, borrowing/inspection, and unchecked arithmetic.

`phase0.incompatible-join` demonstrates the normalized extra-binding layer: `s0` is the primary `select` endpoint from the profile table, while `condition : Bool` is an independent unrestricted binding from `environment-bindings-v1.tsv`.

The validation/provenance tranche uses the same machinery for raw recognition input, `Begin` records, validation evidence, explicit receive/select requirements, an owned payload witness, and the shared opaque `DigestMatches` declaration required for the intended opaque-proof rejection. These are semantic boundary values rather than fixture-name aliases.

The remaining profiles still pass through the transitional Phase-0 compatibility adapter until their richer nested or payload-bearing session environments are encoded in later INT-004 slices. Materialized profiles are forbidden from falling back to that adapter, so deletion or corruption of portable environment material fails closed.

The manifest, not the legacy filename table, owns expected rejection classes. Legacy classification parity remains a migration regression only. Exact diagnostic strings and Haskell exception constructors are not conformance authority; the portable class labels are semantic labels that implementations map to their own diagnostics.
