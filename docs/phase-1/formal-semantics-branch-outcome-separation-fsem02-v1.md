# FSEM-02: checked-source choice branch isolation and End outcome separation

**Status: non-normative, bounded source/Core/model conformance; #1613 remains OPEN.** Follows merged #1732. This is not an independent interpreter, universal refinement or normative promotion.

## Scoped judgment and explicit external inputs

From the same original checked endpoint occurrence `e`, admitted binary protocol projection `Offer{Go => End Done, Cancel => End Cancel}`, source-checked complete server component, original protocol/resource context `P`, and caller-provided selected label, use the existing production `grammarV1ReplayComponentOffer`:

```text
Sigma ; source-offer ; P ; label=Go     |- Offer(e -> e') => P_Done
Sigma ; source-offer ; P ; label=Cancel |- Offer(e -> e') => P_Cancel
P_Done != P_Cancel; both consume e; same e' has distinct End result types
P_Done   ; close(e', Cancel) => rejected(CloseOutcomeMismatch Done Cancel)
P_Cancel ; close(e', Done)   => rejected(CloseOutcomeMismatch Cancel Done)
P_Done   ; Offer(e -> e'', Cancel) => rejected(ProtocolEndpointUnknown e)
```

These are **alternative branches from a single original state**, not simultaneous live successors. Exactly matching, independently authorized End closes eliminate either successor without adding a new one. An otherwise complete source lacking the Cancel arm rejects at the source coverage stage, exactly `GrammarV1ComponentOfferMissingArm "Cancel"`. A source arm's `return unit` is not endpoint close authority. A selected label and fresh successor are caller inputs, not inferred from source scheduling.

## Executable evidence

- Accepted complete source: `test/fixtures/fsem02-source-offer-v1/accepted.phil` — separately parsed, binary family instantiated, projected and source-arm checked.
- Minimally rejected complete source: `test/fixtures/fsem02-branch-outcome-separation-v1/missing-cancel.phil` — exactly one missing offer arm, independently checked against the same admitted role projection.
- `test/Phase1FSEM02BranchOutcomeSeparationMain.hs`: independently runs both labeled source offer replays from the same original real `ProtocolContext`, compares complete states and precise `TyEndpoint (End outcome)` witnesses, checks wrong cross-outcome closes and post-consumption opposite-branch replay against exact native diagnostic constructors, then checks successful authorized terminal clears. It also runs the #1732 arm-order regression witnesses.
- `proof/Phil/Core/FSEM02BranchOutcomeSeparation.v`: Rocq 9.2 conditional finite model theorems for exact two-branch head selection, differing outcomes, predecessor consumption and typed successor identities, wrong-outcome rejection and stale-owner non-success. No new axioms, parameters or admits.

## Trust boundary and outstanding obligations

Already-admitted protocol instance and role projection, exact source binder/name mapping, activation/endpoint ownership, caller label/fresh successor, and two separate End disposal permissions remain explicit premises. The `SessionStep.endpointType` Rocq model is an **abstract token**, not a proof that native `TyEndpoint` equals that token. The Haskell finite test checks production state but is not a Haskell-to-Rocq simulation. No general offer arm body evaluation, payload transfer, architecture/root certification, assurance discharge, fairness or global FSEM-02 completion is inferred.

Focused **GHC 9.6.7 strict warning-free** and **Rocq 9.2 no-new-admissions** independent checks are defined in `.github/workflows/fsem02-branch-outcome-separation-preflight.yml`; full PR CI and exact claim guard are still separate mandatory gates.
