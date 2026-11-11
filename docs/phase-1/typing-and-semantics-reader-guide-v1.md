# Phil Phase 1 typing and semantics: a reader's guide (draft v1)

> **Status: non-normative review draft.** This is a navigational and pedagogical
> document for PL/formal-methods reviewers. It is **not** a new specification,
> a claim of global soundness, or a declaration that Phase 1 is frozen.
> Where it gives schematic inference rules, the established semantic contracts
> and checked models cited below—not this presentation—remain authoritative.
> Last assembled against `main`: 2026-11-05.

## What to read first

Phil is a systems language designed to make *architecture executable and
implementation replaceable*. Its central question is not merely whether a
function can be proved correct, but whether a system's selected components,
protocols, resources, authority, implementation choices, and evidence remain
consistent with the architecture to which they are committed.

There are several layers of authority; they must not be conflated.

| Layer | What is authoritative / what to inspect |
| --- | --- |
| Concrete syntax | [Grammar v1](../../grammar/phase1-surface.ebnf) and its [status document](surface-grammar-v1.md). Parsing alone establishes no semantic validity. |
| Accepted design | Stabilized ADRs and semantic contracts; [syntax/semantics completeness reconciliation](syntax-semantics-completeness-v1.md) explains which author choices require source syntax. |
| Human-readable judgment model | [Phase 0 Core judgments](../phase-0/semantics/core-judgments.md) are normative **for Phase 0**, not an automatically unchanged Phase 1 calculus. This guide explains the continuities and Phase 1 extensions without silently promoting Phase 0 rules. |
| Checked mathematical models | [Rocq corpus](../../proof/README.md) in `proof/Phil/`; individual files state their abstractions, assumptions and obligation IDs. Proof of a normalized model is not automatically proof of its Haskell implementation. |
| Source implementation and conformance | `src/Phil/Surface/`, `src/Phil/Core/`, `test/`, and `app/`; acceptance must be distinguished from syntactic parse success. |
| Current completion status | Project Logic Ledger and Conformance Matrix, plus exact-commit proof/certification and CI evidence. Historical `docs/phase-1/*-v1.md` slice notes are **not** current status authorities: see the [Phase 1 notes README](README.md). |

**Suggested reading route:** [Phase 1 Tour](../tutorials/tour-phase1.md)
→ this guide → the canonical grammar → the judgment/proof links below
→ the specific proof and implementation correspondence for any claim you want
to challenge.

## Worked Phase 1 rule families (companion worksheet)

For three paired accepted/expected-rejected examples and explicitly
**schematic** checking rules, see
[Phase 1 typing rules: resource scope, session progression, and root
architecture validity](typing-rules-worked-examples-draft-v1.md).

That worksheet also records the research-review point that a
progress/preservation argument for a chosen Core semantics is not enough
without typing and behavioral correspondence for each elaboration and
realization boundary. It is a review draft, **not** a newly certified
end-to-end soundness theorem.

## 1. Judgment vocabulary and the checker/assurance boundary

The Phase 0 Core judgment vocabulary is a useful starting point:

```text
Σ ; Γ ; A ; Δ

Σ ; Γ ; A ; Δ ⊢ e ⇒ T ⊣ A' ; Δ' ▷ Φ
Σ ; Γ ; A ; Δ ⊢ e ⇐ T ⊣ A' ; Δ' ▷ Φ
Σ ; Γ ; A ; Δ ⊢ P ⇝ K ⊣ A' ; Δ' ▷ Φ
```

Read this as follows:

- `Σ` is the immutable environment of declarations, contracts, protocol and
  type information, claims, and other checked static facts.
- `Γ` contains unrestricted values/evidence.
- `A` contains affine owners, usable **at most once**.
- `Δ` contains linear owners, required to be accounted for **exactly once**.
- `⇒` synthesizes a type; `⇐` checks against an expected type.
- `A'; Δ'` record residual owners after checking.
- `Φ` contains named, provenance-bearing verification obligations.
- `P ⇝ K` checks a process/control path, whose continuation/return/terminal
  disposition matters for resource closure.

These are **schematic Phase 0 judgments** shown to orient reviewers. The full
Phase 1 static semantics, including architecture and effect/authority
judgments, is distributed across stabilized contracts and Rocq slices. One
deliverable of the final formal specification is to restate them together
without accidentally claiming a theorem stronger than the individual slices.

A crucial rule: **a syntactically valid program, a semantically valid program,
a discharged obligation, and a certified executable are four different
claims.** [Surface grammar](surface-grammar-v1.md),
[the Phase 1 tour, sections 13–16](../tutorials/tour-phase1.md), and
[the proof certification guide](../assurance/rocq-proof-certification.md)
explain those boundaries.

## 2. Structural typing and resource state

Phil distinguishes unrestricted, affine, and linear structural modes.
A value's owning mode is determined by its checked type and resource
contract—not by independently annotating every binder. Transparent aggregate
modes reflect their owned contents, and capabilities separately describe
authority and possession mode.

Representative semantic obligations (not a complete inference-rule set):

```text
unrestricted x : T    => reuse or discard permitted
affine       x : T    => no duplication; discard may be permitted
linear       x : T    => exactly one legal use/transfer/closure

send/consume linear x => x is absent from the subsequent owner context
borrow owner as view  => owner cannot simultaneously be moved or consumed
leaving borrow scope  => view must not escape
```

The precise accounting at a join matters: both continuing branches must
agree on required linear survivors; terminal branches do not manufacture
dummy resources solely to create a join. A successful branch or loop may
carry an explicit continuation-state contract, but such a contract cannot
recreate an already-consumed owner.

Read:
[Phase 0 judgments §§3–6, 13](../phase-0/semantics/core-judgments.md),
[Phase 1 Tour §§2–4](../tutorials/tour-phase1.md),
[Core context model](../../proof/Phil/Core/Context.v),
[process sequencing model](../../proof/Phil/Core/Process.v),
[Core join](../../proof/Phil/Core/ProcessJoin.v), and
[terminal resource closure](../../proof/Phil/Core/ProcessTerminal.v).
The individual Rocq files identify their exact abstraction boundaries; in
particular, one structural-model theorem is not a global soundness theorem
for all source programs.

## 3. Propositions, refinements, and proof obligations

A declaration such as:

```phil
claim Positive(x : U32) = x > 0;
```

names a reusable proposition. **Declaration is not proof.** A refinement
`{v : U32 | v > 0}` demands both a base type check and appropriate
justification of the predicate under the rules at the required point.
`requires`, `ensures`, guards, loop invariants, and architectural constraints
are different sites at which propositions become obligations.

An obligation's admissible outcomes depend on its kind, policy, and boundary.
Static discharge may use definition, matching evidence, or a checked
certificate; certain obligations may be explicitly runtime-bound or exported.
An export is not local proof. An assumption must be declared through an
authorized boundary, **not** inferred from failed verification. Language
invalidity—such as copying a linear owner or an illegal protocol step—cannot
be renamed an assumption to make source valid.

```text
obligation with exact identity, proposition, origin, and required point
  -> checked static evidence          (where permitted)
  -> explicit runtime enforcement     (where permitted, with failure behavior)
  -> explicit export/assumption boundary (where permitted and recorded)
  -> otherwise unresolved or rejected; never silently "true"
```

The Phase 1 ordinary surface language has **no native general-purpose
interactive proof language**. Current proof-assistant integrations use Rocq
to construct and check theorems and to bind certificates to exact Phil
obligations. This does not assert that a Lean certificate adapter already
exists, nor that Phil independently rechecks the Rocq kernel.

Read:
[Phase 1 Tour §§13–15](../tutorials/tour-phase1.md),
[Phase 0 judgments §§10–15](../phase-0/semantics/core-judgments.md),
[focusing](../../proof/Phil/Core/Focusing.v),
[discharge](../../proof/Phil/Core/Discharge.v), and
[Rocq proof certification](../assurance/rocq-proof-certification.md).

## 4. Callables, effects, and authority

A callable's declared *may-effect set* is a **public upper bound** on
observable semantic effects, not a list that must be exercised. An
implementation may have fewer effects but not undeclared wider effects.
Effect labels may identify the particular semantic resource involved.
Bounded effect polymorphism permits a finite actual set only within its
declared upper bound.

The following is a *schematic checking condition*, not a newly introduced
normative judgment:

```text
inferred reachable effects(body) ⊆ public may-effects(interface)
required authority(invocation) ⊆ authority available at invocation
```

The two conditions are independent. Listing `Write(store)` as a permitted
effect does **not** grant permission to write that store. Merely possessing,
passing, storing, or returning an effectful callable is effect-neutral;
actually invoking it contributes its declared public effect bound to the
reachable effect footprint.

Providers model contract-based implementation abstraction and replacement,
but they are **not** general algebraic effect handlers. General
user-written algebraic effect handlers are outside the Phase 1 surface
language.

Read:
[Phase 1 Tour §§5–6, 11](../tutorials/tour-phase1.md),
[callable effect bound](callable-effect-bound-v1.md),
[effect syntax](surface-grammar-v1.md#effect-syntax),
[CallableEffects Rocq model](../../proof/Phil/Core/CallableEffects.v),
and [effect polymorphism Rocq model](../../proof/Phil/Core/EffectPolymorphism.v).

For the first bounded, non-normative FSEM-02 head/endpoint progression
source-and-Core witness, see [FSEM-02 exact local protocol progression](formal-semantics-protocol-progression-fsem02-v1.md).
It is not a source-to-Rocq refinement theorem or a network scheduler model.

The further bounded [source-select/offer joint Core rendezvous](formal-semantics-source-joint-choice-fsem02-v1.md) combines independently parsed component programs with an externally supplied peer choice and a real atomic two-process Core transition. It deliberately does **not** certify combined source architecture/root authority, the restricted endpoint-owner ledger, payload transfer or universal Rocq correspondence.

The [stateful source choice and endpoint-owner ledger bridge](formal-semantics-stateful-choice-fsem02-v1.md) further checks production activation-derived restricted owner occurrences through the atomic stateful Core joint transition. This models endpoint-owner renaming and affine spectator preservation, **not** message-payload ownership transfer or combined-source architecture/root admission.

## 5. Session protocols and communication

A protocol specifies the legal sequence of send, receive, choice, offer,
and terminal events. The executing participant holds a session endpoint
with an **exact current state**. A legal action consumes its predecessor
endpoint and supplies the corresponding successor; closing a terminal
endpoint consumes it. An unrestricted message value such as `U8` does not
become linear merely because its endpoint is linear.

For internal Phase 1 communication, the bounded static network has
**synchronous rendezvous** for matching admitted send/receive participants.
Causality arises from local program order, rendezvous, and explicit
architecture constraints—not an implicit scheduler order. A failed process
does not silently cancel all peers or turn a stuck network into successful
terminal closure.

Protocol safety is not, by itself, a guarantee of fairness, deadlock
freedom, deadlines, or eventual response. Those require separate,
appropriately evidenced claims.

Read:
[Phase 1 Tour §§7–10, 18](../tutorials/tour-phase1.md),
[Core session model](../../proof/Phil/Core/Syntax.v),
[concurrency semantics](../../proof/Phil/Core/ConcurrencySemantics.v),
and its [proof scope and exclusions](concurrency-semantics-proof-v1.md).

The [restricted Send/Receive typed terminal-head witness](formal-semantics-restricted-terminal-heads-fsem02-v1.md) checks actual source/Core endpoint metadata and exact linear `TyEndpoint End` continuations with externally supplied outcomes; wrong heads, stale predecessors and unsupported source reject without successor. This is a bounded, non-normative observation, not global refinement.

The bounded [restricted Send/Receive one-sided End-prefix ledger check](formal-semantics-restricted-close-prefix-ledgers-fsem02-v1.md) independently replays actual production Core prefixes and proves a conditional Rocq owner/payload/spectator model; the terminal authority, payload disposition and architecture/root boundary remain explicit premises.

## 6. Architectures, occurrence identity, and root selection

The source differentiates:

| Form | What it commits to |
| --- | --- |
| `component` | A reusable executable participant definition |
| `architecture` | Named occurrences, process sites, protocols, role assignments, bindings, entries, and boundary decisions |
| `instance` | A distinct occurrence of a declared component/architecture |
| `ref` | An explicit reference to an existing occurrence, **not** a clone |
| `process` | Activation of an already-created executable occurrence in the bounded network |
| `role` | Explicit protocol-role responsibility, internal or `external` |
| `bind` | The exact source of a particular component input |
| `program ... = instantiate ...` | Selection of a fresh root architecture occurrence |

In the [Tour's complete internal Ping example](../tutorials/tour-phase1.md#18-how-the-ping-pieces-fit),
`LocalPing` creates `client` and `server`, activates each once,
assigns both ends of one `ping` protocol, and binds exact endpoint and
payload inputs. The example is a **checked complete source wiring path**,
not a demand that every architecture reproduce those source lines.

A useful negative example: deleting `process server_run = server;` while
still assigning an internal `ping.Server` role to `server` leaves an
internal participant without the required activated process. It must not
be silently reclassified as `external` or accepted as a completed root
network. Similarly, `entry payload : U8;` names a real input from the
surrounding realization; it does not conjure a constant.

There are two deliberately separate stages:

1. **Declaration and local checks** establish the legality of the
   architectural forms and their referenced contracts.
2. **Selected-root construction and whole-network checking** enumerate
   the finite process population and test exact activation, identity,
   role/process/binding, ownership, communication and terminal facts.

Neither stage implies that an arbitrary target binary has already been
certified to preserve them.

Read:
[architecture instantiation](architecture-instantiation-v1.md)
(historical slice—see status caveat),
[syntax/semantics completeness §ADR-024](syntax-semantics-completeness-v1.md#adr-024-concurrency-extension),
[ArchitectureInstantiation Rocq](../../proof/Phil/Core/ArchitectureInstantiation.v),
[ConcurrencySemantics Rocq](../../proof/Phil/Core/ConcurrencySemantics.v),
and the [tour §18](../tutorials/tour-phase1.md#18-how-the-ping-pieces-fit).

## 7. Ordinary execution versus target realization

Phil's source-level control, arithmetic, ownership, protocol, and
architecture commitments are not permissions for a backend to improvise
new observable semantics.

In ordinary source evaluation, explicit sequence order matters. At a
target boundary, the implementation may choose representations, allocation,
thread/event-loop mapping, and other physical mechanisms—but the selected
realization must account for the consequences, including any new effects,
authority requirements, failure cases, costs, and evidence needs.

`SystemsArtifact`, `StageContract`, target runtime carriers, and
artifact certification are **not** source-language syntax. Source
verification and artifact certification have different evidentiary
subjects. A valid source or a valid proof of a normalized Core model
does not automatically establish correctness of a particular compiler,
backend, ABI, operating system, or execution runtime.

Read:
[Tour §§15–16](../tutorials/tour-phase1.md),
[Surface grammar's exclusions](surface-grammar-v1.md#deliberate-non-goals),
and [systems staging-effect accounting](systems-staging-effect-v1.md).

## 8. What exactly has been proved?

The Rocq corpus is extensive, but it is **modular**. A theorem generally
establishes a property of a named, normalized semantic model, frequently
with explicit inputs or a correspondence boundary. One must inspect both
the theorem statement and its implementation bridge before concluding
anything about end-to-end source acceptance or generated machine code.

Examples of evidence and their scope:

| Property to examine | Proof/evidence entry point | Important qualification |
| --- | --- | --- |
| Session structure, duality, and progression | [Syntax](../../proof/Phil/Core/Syntax.v), [session recursion](../../proof/Phil/Core/SessionRec.v), [protocol projection](../../proof/Phil/Core/ProtocolProjection.v) | Message types and implementation representations may be abstract in individual slices. |
| Resource insertion/consumption, sequencing, and joins | [Context](../../proof/Phil/Core/Context.v), [Process](../../proof/Phil/Core/Process.v), [ProcessJoin](../../proof/Phil/Core/ProcessJoin.v) | Models isolate particular checking operations, not the whole source checker. |
| Canonical proposition handling and discharge | [Focusing](../../proof/Phil/Core/Focusing.v), [Discharge](../../proof/Phil/Core/Discharge.v) | Certifier/checker and proposition-normalization competence boundaries must be preserved. |
| Surface elaboration authority | [Surface Elaboration](../../proof/Phil/Surface/Elaboration.v), [Surface Checking](../../proof/Phil/Surface/Checking.v) | These do not purport to verify the Megaparsec parser or every concrete implementation detail. |
| Callable may-effect bounds | [CallableEffects](../../proof/Phil/Core/CallableEffects.v), [EffectPolymorphism](../../proof/Phil/Core/EffectPolymorphism.v) | Concrete effect identities, sets, and source-to-Core correspondence have their own obligations. |
| Architecture occurrence graph | [ArchitectureIdentity](../../proof/Phil/Core/ArchitectureIdentity.v), [ArchitectureInstantiation](../../proof/Phil/Core/ArchitectureInstantiation.v) | Stable occurrence identity is distinct from revision/evidence validity and target realization. |
| Bounded concurrency safety | [ConcurrencySemantics](../../proof/Phil/Core/ConcurrencySemantics.v) | Does **not** establish scheduler fairness, deadlock freedom or eventual progress. |

For any specific theorem, follow its obligation ID to the **current**
Logic Ledger, inspect the precise statement, trace the production binding
(if one exists), and check the exact-commit conformance/certification
artifacts. A green CI test, a certified theorem about a normalized model,
and a general compiler correctness theorem are not interchangeable.

## 9. Review targets and gaps to close

This draft aims to make current work navigable. It intentionally does not
invent a monolithic Phase 1 type judgment or assert a global progress /
preservation theorem for the whole language. To produce an expert-reviewable
formal specification, the next passes should:

1. **Unify the Phase 1 judgment signatures.** Write the normative forms for
   expression synthesis/checking, process path/control checking, resource
   context transitions, callable/effect/authority checking, protocol
   transitions, architecture validity/root selection, and obligation
   disposition. Reconcile every extension with the old Phase 0 notation.
2. **Give syntax-directed rules and failure cases.** Prioritize linear use,
   borrow/join/loop, refinement introduction, session send/receive/close,
   callable invocation, process activation/role binding, and internal versus
   external boundaries. Provide at least one minimal accepted and rejected
   program per family.
3. **State the operational relation.** Explain local step order, selected
   process networks and synchronous rendezvous, failure/terminal/stuck
   distinctions, and which target decisions are outside source semantics.
4. **Build a theorem-to-implementation matrix.** For each rule/theorem:
   authoritative contract, exact Rocq theorem, implementation entry point,
   conformance witness, and the current evidence status. Read status from
   the ledger/matrix rather than from a historical closeout note.
5. **Ask external readers where the presentation overstates or underdefines
   behavior.** In particular: Is authority separate enough from effect
   typing? Are claim/evidence scoping rules explicit? Are architecture
   occurrence and revision identities clear? Can one see why the negative
   Ping example must reject?

### Questions for reviewers

- Which typing judgment or operational rule would you need first to begin
  assessing soundness?
- Which facts currently require jumping between too many source locations?
- Does any statement in this guide wrongly treat a proof about a normalized
  model as a statement about parser/compiler/runtime correctness?
- What is the smallest counterexample that would falsify our stated
  architecture, session, or effect rules?

This guide should become shorter and more exact as the consolidated
judgments and rules are written—not grow into a second, competing
specification.

The bounded [FSEM-02 source-checked restricted payload rendezvous](formal-semantics-restricted-source-transfer-fsem02-v1.md) composes independently parsed typed send/receive source with the existing production Core atomic payload owner transition, exact accepted/rejected source replay, and conditional Rocq owner/endpoint frame lemmas. Non-normative: external nominal/activation authority remains a premise; full architecture admission, source-close execution, and universal Haskell-to-Rocq refinement remain open.

The bounded non-normative FSEM-02 [checked source-close carrier correspondence](formal-semantics-source-close-carrier-fsem02-v1.md) compares the full native request and exact source payload binders while preserving explicit external authority; it is neither a general source-to-Core refinement nor normative.

The bounded [FSEM-02 exact original restricted rendezvous predecessor replay](formal-semantics-restricted-predecessor-replay-fsem02-v1.md) re-executes native send/receive against explicit original Core authority/state and compares the whole successor, not just cached identities; this is non-normative and not universal refinement.

The bounded [FSEM-02 typed terminal heads and both first-End close prefixes](formal-semantics-restricted-typed-head-prefix-fsem02-v1.md) independently replays the same restricted send/receive source and original Core state through typed End head validation and two externally authorized one-sided endpoint retirements. It tests exact negative source, session-head, stale-owner and occurrence-alias diagnoses; Rocq conditionally composes the separate owner-frame lemmas. This is not general source-to-Rocq refinement or a source-derived closure grant.
