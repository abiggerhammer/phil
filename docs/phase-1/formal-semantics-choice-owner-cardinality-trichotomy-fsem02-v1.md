# FSEM-02 — finite End-owner cardinality trichotomy (non-normative)

**Scope:** the actual production `closeProcessEndpointState` at `src/Phil/Core/ProcessEndpointClosure.hs`, following separately checked complete Go/Done and Cancel/Cancel Select/Offer source pairs. The single accepted and minimally rejected executable source witnesses are `test/fixtures/fsem02-source-choice-v1/accepted.phil`, `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil`, `test/fixtures/fsem02-source-offer-v1/accepted.phil` and `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil`. The latter must reject precisely `GrammarV1ComponentOfferArmBodyUnsupported`, not fall back to an opaque source interpretation.

## Explicit transition and authority premises

After the checked Select/Offer atomic predecessor consumption, use the *external* separately activated process keys, checked protocol identity, and externally admitted terminal End outcomes. The source does not grant process activation, a selected architecture root, nominal protocol authority, terminal disposal, scheduler rights or assurance. The local endpoint owner relation is a `Map ActivationOccurrenceKey (ProcessKey, Name)`; the adversarial test modifications to that map are **not source operations**.

For an active process with a context, let `C = [k | (k,(p,n)) <- Map.toList owners, p == requestedProcess, n == requestedEnd]`. The production precedence is:

- `|C| = 0`: **exact `EndpointClosureOccurrenceUnknown p n`**; no successor even with incorrect nominal inputs.
- `|C| = 1`: pass the single occurrence to the *separate* nominal/session Close checker. Wrong instance returns exact `EndpointClosureProtocolError (ProtocolInstanceMismatch ...)`; with authorized End, retire precisely the unique occurrence and checked protocol endpoint atomically.
- `|C| >= 2`: **exact `EndpointClosureOccurrenceAmbiguous p n C`** with the full candidate list in native Map key order, before nominal checking; no retirement.

The finite test executes populations with 0–6 matching owners, including process-only, endpoint-only and entirely unrelated aliases, independently authorized peer-first closure and borrowed affine spectator framing. Its one-match case replays both End orders to the original native terminal diamond. The zero/multi-match cases refuse *also after* an independent peer Close. Crucially, this tests the native implementation for finite inputs, not a proof of universal native Map enumeration completeness.

## Rocq correspondence boundary

`proof/Phil/Core/FSEM02ChoiceOwnerCardinalityTrichotomy.v` proves the finite zero/single/multiple classification, explicitly conditions unique successful retirement on the separately checked owner-retirement result, characterizes the unauthorized single-match failure, preserves complete ambiguity candidates with no successor and establishes an exhaustive finite shape split. Its inputs are an admitted finite owner ledger and enumerated population; **native Map-to-Rocq correspondence is not proven**. The existing `SessionStep.v` and `ConcurrencySemantics.v` remain independently normative only to their previously accepted scope; no new syntax authority is inferred.

No universal Haskell↔Rocq refinement, source elaboration correctness, scheduler fairness/progress/deadlock freedom, external authority inference, normative semantics promotion, or TCB change is claimed. FSEM-02 remains open.
