# Phase 1 portable negative corpus

This directory carries the INT-004 migration from implementation-private negative tests to portable conformance fixtures.

`manifest.tsv` is normative for the migrated frozen Phase-0 semantic negatives. Each row gives a stable fixture identity, portable `.phil` input path, implementation-independent rejection class label, earliest competent rejection layer, explicit environment profile name, and governing Matrix authority.

`environment-profiles-v1.tsv` is the portable representation of profile-level checker environment data. Its fields are semantic data rather than Haskell constructor text or fixture filenames:

- `profile_id` — stable profile identity referenced by `manifest.tsv`;
- `binding_name` / `binding_mode` — the primary architecture-supplied endpoint binding, or `-` when the profile has no inline primary binding;
- `session_kind` — `receive`, `offer`, `select`, or `none`; nested sessions use normalized endpoint bindings from `environment-bindings-v1.tsv` instead of growing an inline mini-language;
- `message_name` / `message_type` / `terminal_outcome` — receive-session data; `message_type` supports `opaque:<name>`, `frame:<grammar>`, `bytes:nat:<n>`, and `bytes:toNat-field:<binding>.<field>:u64`;
- `branches` — semicolon-separated `label:terminal-outcome` entries for compact one-step offer/select sessions;
- `primitive_bindings` — semicolon-separated `source-name:semantic-operation` entries;
- `legacy_receive_frame_raw` — explicit semantic compatibility flag for the old raw-frame receive boundary.

`environment-bindings-v1.tsv` is the normalized repeated-binding layer for profiles that need additional architecture-supplied values beyond the inline primary endpoint. Each row carries `profile_id`, `binding_name`, `binding_mode`, a portable `binding_type`, and `binding_shape`. The vocabulary includes `bool`, `frame:<grammar>`, `validated:<claim>:<context>:<subject>`, explicitly sorted opaque values, and `endpoint-session:<session-id>`, with `plain`, `record:<grammar>`, fixture-raw, and owned-bytes shapes. Duplicate binding names within one profile are invalid, and binding rows may only refer to declared portable profiles.

`environment-session-nodes-v1.tsv` and `environment-session-branches-v1.tsv` are the normalized representation for nested protocol sessions. A session has exactly one root node. Nodes are `receive`, `select`, `offer`, or `end`; receive nodes carry a message name/type and one continuation, while select/offer branches live in the branch table with optional payload name/type and a target node. Every reference must resolve, branch labels are unique at a source node, non-branching nodes may not own branch rows, and all nodes must be reachable from the root. The message/payload vocabulary also includes the selected-version refinement `refined-member-field:u16:<binder>:<record>.<field>:finite-set-u16` used by the frozen upload protocol.

`environment-type-aliases-v1.tsv` carries profile-scoped source type aliases that are actually required at the competent boundary. The final frozen migration uses it to reconstruct `Server[Upload]` from the shared `phase0.server-upload` session graph for the pending-receive fixtures. Alias rows refer to stable session IDs rather than Haskell constructors.

`environment-requirements-v1.tsv` carries competent-boundary proof requirements independently of Haskell maps. Each row names a profile, a requirement site (`receive-exact` or `select`), the site label when applicable, and a portable proposition. Atom arguments may be ordinary variables or explicit opaque witnesses such as `opaque:stable-id-OwnedBytes:payload`.

`environment-static-claims-v1.tsv` carries the corpus-level static claim context inherited by every frozen Phase-0 checking environment. Each row gives a claim name, declaration kind, and ordered parameter list with portable sorts. The corpus declares `DigestMatches` as opaque with `begin : opaque Frame` and `payload_id : stable-id OwnedBytes`. This is portable semantic context, not a Haskell fixture alias; removing or corrupting it must fail closed rather than causing a fixture to reject earlier as an unknown claim.

A literal `-` means the field is not applicable to that profile shape. All portable data is path-free and contains no Haskell implementation identity; another checker can reconstruct the same competent-layer context from these tables alone.

`phase0.common` is intentionally represented as a no-initial-binding profile. The affected fixtures get their resource modes from intrinsic surface types (`StoreCap`, `OwnedBytes`, `U32`) and require only explicit primitive semantics for authority exercise, cancellation allocation, borrowing/inspection, and unchecked arithmetic.

`phase0.incompatible-join` demonstrates the normalized extra-binding layer: `s0` is the compact primary `select` endpoint from the profile table, while `condition : Bool` is an independent unrestricted binding from `environment-bindings-v1.tsv`.

The validation/provenance tranche uses the same machinery for raw recognition input, `Begin` records, validation evidence, explicit receive/select requirements, an owned payload witness, and the shared opaque `DigestMatches` declaration required for the intended opaque-proof rejection.

The final frozen-environment tranche moves `phase0.premature-acceptance`, `phase0.pending-commit`, `phase0.pending-drop`, and `phase0.label-proof` onto normalized nested session graphs. `phase0.pending-commit` and `phase0.pending-drop` share one exact `phase0.server-upload` graph and reconstruct the `Server[Upload]` source alias from portable data. Once this tranche is promoted, no frozen Phase-0 negative environment may fall back to `phase0EnvironmentFor`; missing or corrupt portable material must fail closed.

The manifest, not the legacy filename table, owns expected rejection classes. Legacy classification parity remains a migration regression only. Exact diagnostic strings and Haskell exception constructors are not conformance authority; the portable class labels are semantic labels that implementations map to their own diagnostics.
