# Phase 1 formal semantics: judgment and correspondence inventory (FSEM-00)

> **Status: proposed interface inventory, not a normative Phase 1 specification.**
> This is the first bounded slice of [the FSEM formalization track](https://github.com/abiggerhammer/phil/issues/1613), not a new language rule, a proved theorem, or a statement that Phase 1 has frozen.
> Last surveyed against Phil main on 2026-11-06. Current claim status must be checked against the Logic Ledger, Conformance Matrix, and exact-commit proof/test results.

## Why this document exists

The [typing and semantics reader's guide](typing-and-semantics-reader-guide-v1.md)
and its [worked rule families](typing-rules-worked-examples-draft-v1.md)
explain the current design to reviewers. They intentionally make no claim to
be the source of truth for the formal semantics.

The separate FSEM track must make three relationships explicit:

1. **Source validity:** which syntactic and semantic premises admit a program,
   and which failures are intrinsic source errors rather than assurance debt?
2. **Execution meaning:** how do a checked program and a selected finite
   process network take steps, transfer ownership, observe effects, and
   terminate/fail/block?
3. **Translation competence:** which exact source-to-Core, Core-to-Systems,
   and Systems-to-target transformations preserve those obligations and
   observations, and which parts are only demonstrated by tests?

These are independent claims; no single green check or normalized-model proof
may silently establish the others.

## Authority and notation

- **Syntax authority:** [Grammar v1](../../grammar/phase1-surface.ebnf) and
  [surface-grammar-v1.md](surface-grammar-v1.md).
- **Accepted semantic decisions:** stabilized ADRs and semantic contracts.
  Refer to the current logic ledger/conformance matrix for claim status.
- **Historical reference:** [Phase 0 Core judgments](../phase-0/semantics/core-judgments.md).
  They are normative for Phase 0 only.
- **Mechanized evidence:** [Rocq corpus](../../proof/README.md), by individual
  theorem, normalized model, and obligation ID. A theorem does not automatically
  verify its Haskell counterpart or source extraction.
- **Executable observations:** source/implementation tests in [test](../../test/)
  and exact-commit CI. A fixture's presence is not proof of a particular
  diagnostic or a stronger correspondence statement.

The following is **proposed metanotation**, not currently accepted grammar:

~~~text
Σ       checked declarations, architectural identity and contracts
R       checker resources (Γ unrestricted, A affine, Δ linear, Loans)
Φ       named provenance-bearing obligations
K       continuation, return, explicit terminal or failure outcome
C       a well-defined source/Core runtime configuration (still to define)
O       observable event or explicitly permitted failure

Σ ; R ⊢ e ⇒ T ⊣ R' ▷ Φ        synthesize type and residual resources
Σ ; R ⊢ e ⇐ T ⊣ R' ▷ Φ        check against expected type
Σ ; R ⊢ p ⇝ K ⊣ R' ▷ Φ        check process/control path
C --O--> C'                  one proposed observable semantic step
~~~

The meaning of R and Φ across branching, nested owners, boundary export,
assurance disposition, and target realization still requires an adopted
normative formulation. In particular, the expression C --O--> C' is a **work
item**, not a claim that one such operational relation already exists.

## Working judgment inventory

The IDs below are **FSEM work-item keys**, not Rocq theorem IDs or new logic
ledger obligation IDs. The named links are starting points, not assertions
of full implementation equivalence.

| Key | Required judgment or relation | Existing source/evidence entry point | Still needed before normative graduation |
| --- | --- | --- | --- |
| FSEM-J01 | Structural context formation and fresh binding | [Context.v](../../proof/Phil/Core/Context.v), [Phase 0 judgments](../phase-0/semantics/core-judgments.md) | Phase 1 context domains, concrete-to-model binding representation and well-formedness |
| FSEM-J02 | Resource move, borrow, join, loop, terminal closure | [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v), [ProcessJoin.v](../../proof/Phil/Core/ProcessJoin.v), [borrow scope test](../../test/Phase1GrammarV1BorrowViewScopeMain.hs) | Syntax-directed ownership/loan rules and isolated source-level negatives |
| FSEM-J03 | Bidirectional expression and refinement checking | [Checking.v](../../proof/Phil/Surface/Checking.v), [Elaboration.v](../../proof/Phil/Surface/Elaboration.v), [Tour](../tutorials/tour-phase1.md) | Complete family of source rules and obligation disposition for each supported form |
| FSEM-J04 | Session head step, exact endpoint continuation and close | [SessionStep.v](../../proof/Phil/Core/SessionStep.v), [session syntax](../../proof/Phil/Core/Syntax.v) | Pair action/type admissibility with resource transition; reject stale predecessor at the relevant source layer |
| FSEM-J05 | Selected-root architecture validity, process activation and role binding | [ArchitectureInstantiation.v](../../proof/Phil/Core/ArchitectureInstantiation.v), [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v) | Exact source-architecture extraction and a whole-network validity judgment |
| FSEM-J06 | Callable effects versus authority and obligation provenance | [CallableEffects.v](../../proof/Phil/Core/CallableEffects.v), [AuthorityPossession.v](../../proof/Phil/Core/AuthorityPossession.v), [Discharge.v](../../proof/Phil/Core/Discharge.v) | Source invocation premises, effect identity, authority separation and explicit export/runtime disposition |
| FSEM-J07 | Configuration transitions, failures, terminal/stuck states and rendezvous | [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v), [INT-008 Ping test](../../test/Phase1INT008SourcePingTerminalMain.hs) | Adopt a source operational relation and observations; state environment and scheduler assumptions |
| FSEM-J08 | Translation and artifact realization relations | [Surface elaboration](../../proof/Phil/Surface/Elaboration.v), [concurrency proof scope](concurrency-semantics-proof-v1.md), [proof certification](../assurance/rocq-proof-certification.md) | Typing/authority and behavior correspondence per translation stage; explicit failure/UB/TCB assumptions |

## First three proposed rule-family boundaries

These are **necessary conditions** extracted from existing contracts and
models. They deliberately stop short of asserting sufficient typing rules.

### FSEM-R01 — borrow and exact owner identity

A borrow requires an existing owner with the appropriate structural mode,
a checked view whose identity and lexical region are explicit, and no owner
move/consume while that loan is live. When the region ends, no view or alias
may escape as an owning value and the owner must retain its correct resource
state. Returning the view where an ordinary U64 is required also introduces
a *separate result-type failure*; that is not an isolated proof of loan-escape
rejection.

- Existing positive test entry: [Phase1GrammarV1BorrowViewScopeMain.hs](../../test/Phase1GrammarV1BorrowViewScopeMain.hs), which checks particular binder-scope properties.
- Review example: [ReadId and an expected-invalid variant](typing-rules-worked-examples-draft-v1.md#12-paired-source-examples-borrow-without-escape--illegal-escape).
- **Missing before promotion:** an executable source-negative where return
  types align and the decisive rejection is the escaped loan, plus a
  source/Core correspondence statement for the chosen rule.

### FSEM-R02 — session continuation and terminal close

On a successful legal session action, the exact old linear endpoint is
consumed and, when appropriate, a *fresh distinct* successor carries the
continuation session. Terminal close consumes a terminal endpoint without a
successor. This resource property **presupposes** session head/type matching;
it is not a substitute for it. Transport failure and ownership of a moved
message require their independently declared disposition.

- Model: [SessionStep.v](../../proof/Phil/Core/SessionStep.v) explicitly treats
  the session matching and concrete endpoint type checks as out of scope.
- Test starting point: [source Ping terminal test](../../test/Phase1INT008SourcePingTerminalMain.hs)
  observes a checked source-derived Ping path and some negative behavior.
- **Missing before promotion:** isolated accepted/rejected complete source
  witnesses for stale endpoint and nonterminal close, and the combined
  source action + resource correspondence rule.

### FSEM-R03 — selected-root process population

A selected root with internal participants must account for exact process
occurrences, activation keys/targets, role assignments, and input bindings.
No internal role target may silently become external merely because an
activation is missing. The normalized bounded-network validity predicate
is an ingredient, not proof that source-to-population extraction is correct.

- Model: [ConcurrencySemantics.v](../../proof/Phil/Core/ConcurrencySemantics.v)
  defines StaticPopulationValid and explicitly excludes fairness, deadlock
  freedom, and eventual response.
- Test starting points:
  [grammar static network test](../../test/Phase1GrammarV1StaticProcessNetworkMain.hs)
  and [source Ping terminal test](../../test/Phase1INT008SourcePingTerminalMain.hs).
  Parsing a named process is not proof that the selected root is valid.
- **Missing before promotion:** positive complete Ping, an executable
  semantic negative with internal server activation removed, and the exact
  bridge from source role/bind identities to the checked process population.

## Translation/proof boundary ledger (initial, incomplete)

| Boundary | Questions to discharge | State in this inventory |
| --- | --- | --- |
| Grammar text → parsed syntax | Does supported text parse deterministically and preserve all proof-relevant identity/spans? | **Map** existing parsing and correspondence slices; not asserted globally here |
| Parsed surface → Core | Is elaboration total-or-explicit-rejection on admitted forms? Does it preserve typing, ownership, effects, authority and observations? | Existing [Elaboration.v](../../proof/Phil/Surface/Elaboration.v) proves selected fragments with a parser boundary; **global bridge open** |
| Core checking → Systems/StageContract | Does lowering preserve obligations, identity, selected process population, permitted effects/failures and certification subject? | **Inventory pending**; do not infer from any one normalized proof |
| Systems → target/ABI/runtime | Are representation choices, traps/UB, foreign calls, and residual authority/costs explicitly admitted and evidenced? | **Target-specific correspondence required** |
| Proof/certification inputs → acceptance | Are propositions, exact heads, toolchain and artifact identities matched to checked evidence? | [Proof certification guide](../assurance/rocq-proof-certification.md) is a starting point; no new authority assumed |

A genuine progress/preservation statement needs **actual** configuration,
typing and step definitions, explicit stuck/failure classifications, and the
right assumptions. Local type preservation alone cannot establish that an
arbitrary elaboration or generated binary behaves correctly.

## Acceptance and evidence rule

Before marking any FSEM rule as adopted, its subsequent PR must provide:

1. A proposed *fully scoped* judgment/rule with explicit premises, outcomes,
   resource/authority effects, and negative cases. Identify the accepted
   semantic authority and any proposed ADR change.
2. An accepted and a diagnostically isolated rejected **executable**
   Grammar-v1 program (or clearly bounded model-level test if source is not
   yet representable); cite the exact test name and commit on which it ran.
3. A theorem/evidence reference with a concrete statement and stable existing
   obligation ID, or an explicit **open** marker. Never invent a new
   obligation ID as though it had ledger authority.
4. A statement of the implementation/translation correspondence **and its
   exclusions**, including parser, representation, scheduler, target/runtime,
   proof producer, and TCB boundaries where applicable.
5. Review before elevating provisional text to normativity. Updates to the
   Logic Ledger and Conformance Matrix must reflect actual checked evidence.

## Next slices

- **FSEM-01:** start with ownership/borrowing, using the existing tests to
  design an isolated executable loan-escape rejection and a concrete source
  resource-state judgment. Keep this distinct from current unrelated proof
  or audit hamsters.
- **FSEM-02:** session progression and terminal closure, with head-action
  versus resource-step assumptions separately represented.
- **FSEM-03:** selected-root validity, including exact internal activation
  and complete Ping wiring.
- **FSEM-04+:** operational relation and elaboration-preservation proofs
  follow once their source and target judgments are agreed.

This inventory is a work coordination artifact. It must **not** become
a competing source-language definition simply by accumulating prose.
