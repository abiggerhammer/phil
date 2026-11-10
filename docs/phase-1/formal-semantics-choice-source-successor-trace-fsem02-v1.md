# FSEM-02: select/offer source-relative successor and terminal owner trace (bounded v1)

**Status: non-normative, FSEM-02 still open.** Tracks [#1613](https://github.com/abiggerhammer/phil/issues/1613). Distinct from the [restricted Bytes[8] source trace](formal-semantics-source-successor-trace-fsem02-v1.md), this slice covers a source-checked **Select/Offer** action, with both `Go` and `Cancel` branches and their different terminal `Outcome` values. It adds no syntax, TCB or normative authority.

## Partial judgment, source competence and trust inputs

For separately parsed Grammar-v1 selector and offer component declarations, explicitly supplied declaration roots, a checked binary protocol instance, externally granted role and process identities, an activated network plus ORIGINAL communication state `Σ₀`, selected peer label, **external Server successor identity**, two distinct externally supplied endpoint occurrence identities and independently authorized Client and Server terminal outcomes:

```text
source Client + source Server ; Σ₀ ; external instance/roles/peer label
  -- checked joint Select/Offer; exact owner transition --> Σ₁
Σ₁ -- Client End --> Σc -- explicitly authorized Server End --> Σcs
Σ₁ -- explicitly authorized Server End --> Σs -- Client End --> Σsc
accept iff full Core Σcs = Σsc and the exact owner trace is:
  original (Client, source Client old) / (Server, source Offer old)
  -> (Client, source Client successor) / (Server, external offered successor)
  -> both occurrence keys retired, every other owner unchanged.
otherwise return precise source/Core/trace rejection with NO successful state.
```

The production `grammarV1CheckChoiceSourceSuccessorTrace` in `src/Phil/Surface/GrammarV1/ComponentChoiceStatefulRendezvous.hs` **rechecks both parsed sources** and executes the existing `grammarV1CheckSourceChoiceCloseDiamond` from original `Σ₀`. Its underlying Core choice action checks exact live projected Select/Offer heads, protocol instance/roles, successor freshness and predecessor consumption. The diamond independently executes the real Core close transitions in both orders and requires equality of the **entire** communication state, not just the owner map.

The additional trace checker compares the **complete** restricted occurrence owner map before and after the action and after both End orders. It refuses aliased occurrences before progression; checks old endpoint identities against their declaration-rooted checked source binders; and requires the two exact new owner identities plus framing of every other occurrence (including an affine spectator). Unlike the source Client successor, the Server successor is an **explicit caller parameter** checked by Core; the return-unit offer arm is not a source Server close or a nominal End grant. A failed check returns `Left`, not an opaque fallback or a purported successor.

## Executable source and negative evidence

`test/Phase1FSEM02SourceJointChoiceMain.hs` uses the existing full parsed `test/fixtures/fsem02-source-choice-v1/accepted.phil`, `test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil`, and `test/fixtures/fsem02-source-offer-v1/accepted.phil` components. The separately checked protocol/activation premises are visible in its fixture. Tests replay Go/Done and Cancel/Cancel twice, compare the independent diamond, original/ready/terminal complete owner maps, and preserve an unrelated affine spectator.

The minimally rejected parsed `test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil` changes the offer-arm body but retains the checked complete-source shape. Its exact rejection is `GrammarV1ComponentOfferArmBodyUnsupported` wrapped by `GrammarV1OfferReplayCoverageError` and the source/diamond error constructors, not a generic parser failure. Additional tests reject a fabricated external endpoint occurrence (`ChoiceSourceTracePredecessorMismatch`), two aliased occurrence keys (`ChoiceSourceTraceAliasedOccurrence`), a consumed/stale source predecessor (`ProtocolEndpointUnknown` nested under the source replay failure), and an incorrect externally supplied Server End outcome (`CloseOutcomeMismatch`). These concrete tests do not prove universal error preservation.

## Conditional Rocq result and limitations

`proof/Phil/Core/FSEM02ChoiceSourceSuccessorTrace.v` composes `fsem02StatefulSourceChoice`, `fsem02RetireSelectedClientOwner`, `fsem02RetireExplicitPeerEnd`, and the conditional `fsem02ConditionalTerminalCloseDiamond` already linked to the abstract `SessionStep.v` and `ConcurrencySemantics.v` corpus. Given **successful** modeled choice and **both** externally authorized close orders, the theorem proves exact model successor endpoint owners, both retirements, spectator framing from the **original** owner ledger and pointwise equality of the two final ledgers. Separate theorems show no modeled second close of a retired Server occurrence and refusal of aliased owner keys. Proof claims require Rocq 9.2 compilation with no new Admitted/Axiom/Parameter.

This does **not** show that arbitrary Haskell `Map` states refine Rocq functional owner ledgers, that a source offer arm closes/disposes an endpoint, that an arbitrary source program is elaborated, or that process/root termination, message admission, effects, authority or assurance are discharged. Selection/activation, all nominal identities, peer scheduler label and Server close authorization are explicit external premises. The family remains open pending wider protocol-rule coverage and independently reviewed correspondence.

**Focused pre-PR checks:** `.github/workflows/fsem02-choice-source-successor-trace-preflight.yml` runs warning-free production Haskell with exact accepted/rejected source tests and Rocq 9.2 conditional proof/absence-of-admissions checks. Full exact-head PR CI, fresh post-ready claim guard, and protected merge are separate requirements.
