# Phase 1 audit proof correspondence: direct named-evidence event authority

Lineage: `D-CERT-SUPPORT-01`, following the direct named-evidence authority proof and the implementation repair merged in #1372.

## Audit boundary

`DirectNamedEvidenceAuthority.v` establishes the semantic authority needed for a directly selected named proof: the immutable evidence record used by the final consumer must preserve the authoritative proposition, semantic subject identity, and scope.

That proof intentionally used `DirectEvidenceName` as its selected domain and left concrete source/check-event association as an implementation-correspondence premise. The landed Phase 1 implementation now makes that premise concrete by keying direct authority with the exact `(ObligationId, Name)` pair. This matters because display names are reusable: two checking events may both select a proof called `proof`, while requiring distinct immutable evidence records or scopes.

## Proof slice

`proof/Phil/Assurance/DirectNamedEvidenceEventAuthority.v` adds the missing event dimension to the bounded proof model.

The new authority relation requires every selected `(check event, evidence name)` pair to preserve:

- the event's authoritative proposition;
- the event's semantic subject identity;
- the event's scope identity;
- the event+name mapping to one immutable evidence record; and
- use of that exact record by the final consumer for the same event.

The negative witness selects the same display name at two different events and deliberately uses a name-only mapping for both. Both events reach a mapped immutable record and a consumer, but the second event's required scope differs from the reused record. The preceding name-level intuition is therefore insufficient once event identity is omitted.

The positive witness selects the same display name at both events while mapping `(event 7, name 1)` and `(event 8, name 1)` to distinct immutable evidence records with the corresponding scopes. It preserves valid name reuse while making substitution across checking events impossible.

## Concrete correspondence

The proof is the model-side counterpart of #1372's concrete authority map keyed by `(ObligationId, Name)`, its exact proposition/subject/scope validation, and its final direct-evidence closure map. It does not claim that the proof imports or verifies Haskell code directly. The implementation regressions remain the evidence for the concrete adapter; this theorem records the semantic contract that adapter must continue to satisfy.

Selected-consumer endpoint coverage, original-event-to-residual-forest completeness, and certificate `EvidenceFact` authority remain complementary obligations. This slice does not duplicate the dedicated Surface Rocq refinement lane or modify implementation remediation.

## Phase 1 boundary

Proof/docs/workflow only. No Haskell production code, ownership/loan state, source admission, native lowering, LLVM, packaging, or Phase 1 trusted-computing-base boundary changes are included. LLVM and the other frozen Phase 1 trusted components remain trusted as specified by the charter.
