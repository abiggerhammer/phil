# FSEM-02 — ordered terminal End triple-fault recovery (non-normative)

Tracking [#1613](https://github.com/abiggerhammer/phil/issues/1613). This
bounded slice composes the distinct gates from the existing missing-context,
linear-resource and terminal-outcome slices, without redefining any of them.

## Exact source/native observation boundary

The original parsed and checked Go/Done and Cancel/Cancel Select/Offer sources
are independently admitted through the production Grammar-v1 checker and Core
rendezvous. The minimally rejected wrong offer-arm body remains an *exact*
`GrammarV1ComponentOfferArmBodyUnsupported` source witness, not an arbitrary
parse failure.

For each Client and Server independently, the executable regression
`choiceTerminalTripleFaultLadder` starts with the checked original live terminal
End and owner occurrences. It constructs **three separate, adversarial Core
resource mutations**: missing linear End, wrong `TyBool`, and wrong End session.
While the malformed context is deliberately hidden entirely, both correct and
wrong external Close outcomes must reject **first** with exact
`EndpointClosureMissingProtocolContext`. Reinstating only the malformed
context must expose the specific resource error *before* outcome checking:
`ProtocolEndpointResourceMissing`,
`ProtocolEndpointResourceTypeMismatch`, or
`ProtocolEndpointSessionMismatch`. Reinstating the **original checked**
context must still reject a wrong supplied outcome with precise
`CloseOutcomeMismatch`. Only the correct, separately supplied outcome allows
the original authorized Close.

An independent peer-first End retirement must leave the faulty process's
owner unchanged and preserve the borrowed affine spectator. At every stage,
the full native final result after explicit restoration and correct Close
must equal the independently checked Client-first/Server-first diamond.

The mutations and restorations are **test inputs**, not source commands,
backtracking, rollback transitions, disposal grants, or new nominal protocol
authority. No proof of source-induced process deactivation is attempted.

## Machine-checked conditional model

`proof/Phil/Core/FSEM02ChoiceTripleFaultGate.v` composes the explicit
missing-context premise with the previous finite resource/outcome model.
Eight conditional Rocq 9.2 lemmas cover context-first refusal, absence of a
retired successor, exact three resource refusal classes, wrong-outcome
retention after resource restoration, and separately granted owner
retirement. These are *finite model implications*, not a derivation of
native owner enumeration, real process activation, resource-map
correspondence, arbitrary scheduler behavior, or universal Haskell/Rocq
refinement.

External protocol/instance/role admission, exact activation and occurrence
ownership, selected-root/disposal authority, proof assurance, and accepted
source contracts remain independent premises. Phase 1 grammar and TCB
are untouched. FSEM-02 remains **open and non-normative**.
