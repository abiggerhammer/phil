# Phase 1 protocol Message admissibility proof v1

This note defines the bounded Rocq proof authority for `PHIL-PROT-MSG-001`, covering the already implemented/tested PROT-008 Message-admissibility boundary landed in #360.

## Certified semantic surface

`proof/Phil/Core/ProtocolMessageAdmissibility.v` models Message competence independently of structural ownership transfer.

It proves:

- scoped shared views are never admissible Messages;
- live endpoint and live authority semantic shapes are never admissible Messages;
- aggregate wrapping cannot launder a forbidden semantic constituent, because successful aggregate-shape admission entails admission of every child;
- Core endpoint and pending-receive types are hard failures even if an external semantic classifier incorrectly labels the value as an admitted leaf;
- product/refinement type wrapping cannot hide an endpoint from the hard-type gate;
- bare concrete session-message types are restricted to the intrinsic Unit/Bool/UInt/product/refined subset;
- an explicit boundary Message contract has a nonempty revision and is tied to the exact actual type and semantic identity;
- type/semantic mismatch, forbidden shape, or hard-type failure rejects;
- successful parameterized protocol instantiation entails successful Message admission in addition to generic discharge; and
- later restricted-owner transfer is a separate downstream predicate: successful transfer entails Message admission **and** separate ownership-transfer authority, while Message admission alone cannot authorize a failed transfer.

This formalizes the Phase 1 no-remote-delegation boundary. Ordinary identifiers/tokens/data may be represented at a boundary, but wrapping or structural movability cannot recreate endpoint/channel or live-capability authority.

## Deliberate abstraction

The Rocq theorem uses normalized `MessageShape`, `MessageType`, contract, generic-discharge, and ownership-transfer values. It does **not** claim mechanical correspondence to the concrete Haskell `Ty`, `SemanticForm`, `Text`, list traversal, or diagnostic path representation.

Phase 1 also deliberately defers remote endpoint/channel passing and distributed capability delegation. A future explicit transfer/reauthorization semantics would be a new obligation, not an implicit extension of this proof.

## Executable correspondence pressure

The dedicated workflow typechecks the unchanged implementation and reruns the existing corpora:

- `test/Phase1ProtocolMessageAdmissibilityMain.hs` for the 11 focused PROT-008 admission/rejection cases;
- `test/Phase1ProtocolProjectionMain.hs` to keep protocol-family instantiation/projection behavior under pressure; and
- `test/Phase1RestrictedMessageTransferMain.hs` for the downstream CONC-005 restricted-owner transfer cases.

Those tests remain implementation evidence; they are not substituted for the Rocq theorem.

On green, `PHIL-PROT-MSG-001` may be upgraded from `Active / Tested` to `Discharged / Certified`. Mechanical production correspondence remains a later `Implementation Refined` concern under `PHIL-ASSURE-IMPL-CORR-001`.
