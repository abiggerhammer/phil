# Phase 1 generic requirement stability v1

> **Historical slice note:** This document records the scope and status of one Phase 1 implementation slice when it landed. “Not yet,” “deferred,” and similar status statements below are historical; see the [Phase 1 implementation notes](README.md) for current status ownership.

This slice begins logic-ledger obligation `PHIL-GEN-REQ-001` and conformance cases `GEN-004`–`GEN-006`.

It distinguishes two structural requirement views for a checked generic definition:

- the **induced minimum** computed from the current checked body; and
- the **published requirement set** that forms the stable public generic contract.

With no explicit public declaration, the published set is exactly the induced minimum. Source or tooling may intentionally publish a stronger set for API stability or architectural intent. That stronger declaration is preserved even when the current body does not need every published permission.

A body revision is accepted under an existing published contract only while every newly induced structural permission is already present in that contract. If the body begins requiring a permission not published by the interface, checking rejects until the interface is revised or the body is changed.

Omitted published requirements mean no permission for that parameter; nothing is inferred into the public contract behind the author's back. Parameter identities remain stable checked keys, and requirement sets remain canonical mathematical sets rather than source-order-sensitive lists.

This slice covers structural requirements only. It does not yet implement provider, callable, proposition/evidence, authority, representation, placement, cost, or assumption requirements; final generic surface syntax; generic application identity; assurance reuse; or generic lowering.

No Rocq proof is claimed yet for `PHIL-GEN-REQ-001`.
