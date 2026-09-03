# PHIL-GEN-KIND-001 — implementation-refinement staging

This tranche stages an executable Rocq decision kernel for the Certified generic static-actual kind semantics without changing production Haskell behavior.

## Certified surface retained

The existing `GenericStaticKind.v` theorem family remains authoritative for GEN-013:

- a direct static actual is admissible only at the exact declared parameter kind;
- a name-shaped static reference is resolved only at that expected kind and is never retried under another semantic category;
- unresolved references reject;
- wrong-kind-only references reject rather than falling back;
- multiple same-kind matches are ambiguous and reject;
- accepted checked actuals preserve the exact parameter key and declared kind; and
- accepted telescopes preserve exact arity and declared key/kind shape.

## Extracted executable seam

`GenericStaticKindImplementation.v` extracts three bounded decisions.

1. `decideDirectStaticActualByFact` owns direct-kind accept/reject.
2. `decideReferencedStaticActualByFacts` preserves native rejection precedence: unresolved name, wrong expected kind, same-kind ambiguity, selected semantic-form mismatch, then acceptance. Under explicit reflection hypotheses its acceptance is equivalent to Certified `ReferenceResolves`.
3. `decideCheckedStaticActualShapeByFacts` is a fail-closed postcondition requiring the checked result to retain the exact declared parameter key and kind; Certified acceptance proves that postcondition.

The extracted kernel does not parse source, construct semantic candidates, choose names, or perform kind-specific semantic lookup.

## Native representation boundary

The later production binding deliberately leaves these facts native and explicit:

- `GenericStaticParameterKey`, `Text`, `SemanticForm`, and `GenericStaticKind` representation/equality;
- duplicate parameter detection;
- telescope length calculation and native list traversal;
- construction and ordering of `GenericStaticReferenceCandidate` values;
- name equality and expected-kind candidate filtering;
- selected candidate semantic-form extraction;
- kind-specific semantic competence behind candidate construction;
- concrete diagnostic payloads/order; and
- checked-result construction.

Native failure always wins. A future kernel disagreement may only add a fail-closed rejection and may never turn a native rejection into acceptance.

## Staging gate

The dedicated workflow recompiles the Certified proof plus implementation correspondence under Rocq 9.2.0, fresh-extracts `GenericStaticKindKernel.hs`, records exact proof/kernel identities, strict-typechecks the generated kernel and direct harness, executes fourteen direct decision controls, strict-typechecks unchanged production GEN-013, and reruns the unchanged GEN-013 corpus.

A green staging merge leaves `PHIL-GEN-KIND-001` at `Discharged / Certified`. Production binding of the exact extracted kernel into `Phil.Core.Generic.StaticActual` is required before promotion to `Implementation Refined`.
