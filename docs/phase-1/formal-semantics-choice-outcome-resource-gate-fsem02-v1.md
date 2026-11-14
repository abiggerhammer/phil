# FSEM-02 — terminal End outcome/resource precedence (non-normative)

This bounded slice reuses the independently parsed and production-checked
Go/Done and Cancel/Cancel client Select / server Offer sources in
test/Phase1FSEM02SourceJointChoiceMain.hs. The complete minimally rejected
offer-body fixture still has exactly GrammarV1ComponentOfferArmBodyUnsupported.
No nominal protocol/role, activation, selected root, or outcome authority is
derived from the source's spelling.

## Native Core failure order and explicit premises

For each source-derived terminal End process, the actual production
closeProcessEndpointState first checks active process, local protocol context,
unique exact process/endpoint owner, and nominal instance/role. The production
checkProtocolAction then checks endpoint metadata versus live linear resource
before the separately supplied Close outcome is tested by the Session step.

The new executable regression exercises both Client and Server, both accepted
branches, and the following adversarial Core-only resource edits: delete the
linear End; replace it with TyBool; replace its End outcome with the other
branch's End. Each edit is paired with both the *correct* and an independently
*incorrect* externally supplied terminal outcome. Every double-fault request
must reject with its exact resource diagnostic
(ProtocolEndpointResourceMissing, ProtocolEndpointResourceTypeMismatch,
ProtocolEndpointSessionMismatch), never silently continue to the wrong
outcome. With the original checked resource intact, the same wrong outcome
must reject as ProtocolSessionError (CloseOutcomeMismatch expected supplied).

Independent peer-first Close must preserve the target's faulty local context,
unconsumed exact owner and unrelated affine spectator. Reinstating the
independently checked original local context is an **explicit external test
operation**, not a source transition or implicit rollback. It removes only
the resource fault; the wrong supplied outcome still refuses. Supplying the
correct outcome then recovers the previously checked full two-order End-close
diamond, including native state equality and spectator framing.

## Conditional Rocq boundary

proof/Phil/Core/FSEM02ChoiceOutcomeResourceGate.v defines a separate finite
owner/nominal/resource/outcome gate. Nine conditional Rocq 9.2 theorems prove
resource refusals take precedence over wrong outcomes, exact no-successor
refusal, owner and nominal precedence, and retirement only with unique owner,
matching outcome/resource and a separately supplied owner-retirement premise.
They do **not** prove a universal correspondence between native Haskell Maps,
Session errors and the finite Rocq observations.

The model never grants actual protocol authority, disposal, scheduler
progress, architecture-root validity, proof assurance or runtime certification.
No normative syntax, TCB change, new Axiom/Parameter/Admitted, universal
Haskell-to-Rocq refinement theorem, or FSEM-02 completion claim.
