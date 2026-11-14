# FSEM-02 — terminal End resource-map agreement gate (non-normative)

**Independent executable sources.** test/Phase1FSEM02SourceJointChoiceMain.hs
checks the real Go/Done and Cancel/Cancel Select/Offer source fixtures
(test/fixtures/fsem02-source-choice-v1/accepted.phil,
test/fixtures/fsem02-source-joint-choice-v1/client-cancel.phil,
test/fixtures/fsem02-source-offer-v1/accepted.phil) before building
the actual production Core joint successor. The complete minimally rejected
test/fixtures/fsem02-source-offer-replay-v1/wrong-body.phil still has the
exact GrammarV1ComponentOfferArmBodyUnsupported class, not a parse-only
or opaque-fallback rejection.

## Bounded native rule and failure order

For each process-local terminal End after an independently accepted
Select/Offer, the native closeProcessEndpointState requires:
an active process; a present process-local protocol context; exactly one
owner occurrence matching the process **and** End endpoint; a matching
externally provided protocol instance and role; agreement between that
endpoint's metadata session and its *linear resource*; and a separately
supplied matching terminal outcome. Only successful checking retires
the matching owner and local linear endpoint together. Rejection returns
no successor state.

A deliberately adversarial Core test changes **only** one side's checked
linear resource map, leaving endpoint metadata, exact restricted owners,
process activation and the peer's checked context intact. Three separately
checked failures are:

- Deleted linear End: precise EndpointClosureProtocolError containing
  ProtocolEndpointResourceMissing.
- Replaced linear End by TyBool: precise EndpointClosureProtocolError
  containing ProtocolEndpointResourceTypeMismatch.
- Replaced linear TyEndpoint (End Done/Cancel) by the opposite End:
  precise EndpointClosureProtocolError containing
  ProtocolEndpointSessionMismatch with both expected and actual End.

The same cases run against both Client and Server, for both accepted
branches. Each also checks that a foreign instance request is refused
*before* the resource mismatch. The unaffected peer can independently
Close; the damaged owner's exact refusal and borrowed affine spectator
persist afterward. **Explicit external restoration** of the original
independently checked local context (not a source step or implicit rollback)
recovers the exact full native two-order Close diamond.

## Conditional Rocq model and limits

proof/Phil/Core/FSEM02ChoiceResourceAgreementGate.v supplies a finite
owner-ledger gate with explicit external nominal and resource-agreement
observations. Its eight lemmas establish exact missing/wrong-type/wrong-
session model refusals; absence of retired successors; owner-cardinality
and nominal precedence; and conditionally successful retirement when the
resource observation, unique owner, and independent retirement premise all
hold. These are **not** formal proofs that native Map, metadata and
resource context satisfy the observations. Haskell tests independently
check the *specific* native error variants; Rocq abstracts those payloads.

Neither adversarial resource mutation nor restoration is permitted by
the accepted source. Protocol instances/roles, architecture activation,
root selection, terminal disposal authority, runtime scheduling, proof
assurance and source-to-Core representation correspondence remain
separate external premises. There are no new admissions, global
Haskell-to-Rocq refinement results, normative syntax changes or TCB changes.
**FSEM-02 remains open and non-normative.**
