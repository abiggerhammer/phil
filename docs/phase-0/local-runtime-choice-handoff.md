# Local runtime choice handoff

This slice is intentionally Systems-only.

It introduces a local branch-payload representation for `choose_supported`, preserves `server.selected_version : UInt16` on the `some` arm, and makes the historical generic `select version` operation consume that exact value.

It does **not** yet normalize `select version(version)` to `OpSessionSelect`, does not normalize the client's `version(selected)` receive, and does not select a wire representation.

The immediate successor slice is semantic normalization of `version(selected)` across both endpoints.
