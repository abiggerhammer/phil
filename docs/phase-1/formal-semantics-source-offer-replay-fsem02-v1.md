# FSEM-02 / bounded source-offer unit-arm branch replay

**Non-normative; FSEM-02 remains open.** Follows the label-completeness
slice in #1680; tracks issue #1613. This slice does not alter the Phase 1
syntax authority, normative semantic contracts, TCB, or proof scope.

## Conditional executable judgment

For a complete parsed Grammar-v1 protocol/component/program witness, an
independently source-derived binary protocol family is strictly instantiated.
The external caller supplies the precise Server role, a selected branch label
and a fresh successor name; they are **inputs**, not inferred peer messages.

The production ComponentOfferCoverage checker resolves the exact endpoint
component parameter and accepts **only** a total duplicate-free set of simple
payload-free offer arms, each with exactly one literal return-unit body.
The ComponentOfferReplay bridge derives the local projection via the actual
BinaryProtocolInstance and rejects missing/ill-formed source bodies. It
requires the live Core endpoint's local session to equal that projection,
then invokes the actual Core checkProtocolAction for its chosen label.

    checked source catalog, exact instance/role projection, live endpoint,
    external label l in source catalog, external fresh successor n
       |- offer e { l_i => return unit } --l--> Core.OfferStep(e,n,l)

The post-state consumes the exact source-rooted predecessor, inserts a
typed successor with the same instance/role and the chosen End outcome,
and preserves the terminal close obligation. Literal return unit in the
source arm does **not** automatically close the endpoint. This is a bounded
local *replay of source-selected branch progression*, not execution of
general statements or full source operational semantics.

## Negative classes and proof boundary

The independent executable
test/Phase1FSEM02SourceOfferReplayMain.hs uses source-checked complete
offer programs for both Go and Cancel. The minimally rejected complete
fixture test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil
changes only a Go arm from return unit to return true, and must reject as
GrammarV1ComponentOfferArmBodyUnsupported (wrapped as a replay
coverage error when invoked through the bridge). Additional tests reject
an unlisted external label, a stale predecessor, a nonprojected live
session head, a wrong protocol instance and a wrong role. Neither a
wrong-head match nor a failed selection invents a successor.

Rocq 9.2 proof/Phil/Core/FSEM02ProtocolHeadProgression.v defines a
model-level finite source-label membership gate and proves conditional
selected-label progression, unlisted-label failure and same-name
predecessor/successor rejection. Actual Haskell runtime-to-Rocq
correspondence is tested only for the named finite fragments, **not**
universally proved.

**Open:** source continuation-body execution beyond this unit marker,
actual source control-state transitions, network offer/select rendezvous
and scheduling, payload/restricted-message transfer, full architecture
root/role admission, global resource invariants, source-to-Core
simulation, complete FSEM-02 and FSEM-05/06/07 discharge.
