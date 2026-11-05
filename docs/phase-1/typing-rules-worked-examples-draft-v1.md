# Phase 1 typing judgments: three worked rule families (review draft)

> **Status: non-normative formalization worksheet, 2026-11-05.** This document
> is a reader-facing reconstruction of **selected** checking obligations from
> the existing Phil semantics, not a newly accepted calculus, a complete
> syntax-directed Phase 1 type system, or a global progress/preservation proof.
> Where a rule is written in inference-rule style, its premises are a
> *presentation* of the checks documented in the linked authoritative sources.
> Precise Core/Rocq models and stabilized contracts control their meaning.
> Source examples marked “expected accepted” are drawn from the Phase 1 Tour;
> rejected variants are deliberately minimal **semantic negatives** derived
> from those examples. This document does not claim to have executed the
> compiler against each edited negative variant.

This worksheet expands the [typing and semantics reader's guide](typing-and-semantics-reader-guide-v1.md).
The intended reviewer question is: **What exact premise makes this accepted,
and what exact missing premise makes the nearby program invalid?**

## 0. Conventions and scope

Start with the [Phase 0 Core judgment vocabulary](../phase-0/semantics/core-judgments.md);
**its authority is Phase 0**. The following derived presentation is not
silently promoted into normative Phase 1 grammar or rules:

```text
Σ ; Γ ; A ; Δ ⊢ e ⇒ T ⊣ A' ; Δ' ▷ Φ   (synthesize)
Σ ; Γ ; A ; Δ ⊢ e ⇐ T ⊣ A' ; Δ' ▷ Φ   (check)
Σ ; Γ ; A ; Δ ⊢ P ⇝ K ⊣ A' ; Δ' ▷ Φ   (control flow)
```

- `Σ`: checked declarations/contracts and semantic identity;
  `Γ`: unrestricted bindings; `A`: affine owners; `Δ`: linear owners;
  `Φ`: provenance-bearing outstanding obligations.
- `R = (Γ, A, Δ, Loans)` abbreviates a **checker resource context**, not
  a first-class Phil type. `R ─action→ R'` below denotes an admissible
  resource transition and is **not** a small-step execution theorem.
- `valid(Pop, Activation, Roles, Binds, ...)` abbreviates a conjunction of
  specified architecture checks; it is **not** claimed to be a newly
  implemented single predicate.
- `reject` means ordinary semantic invalidity, *not* an unresolved proof
  obligation that assurance policy can admit.
- In source diffs, the “accepted” baseline is exactly the linked Tour
  program unless a shortened excerpt is explicitly identified as a
  fragment. Comments and diff markers are explanatory, not Phil syntax.

At minimum, a complete account needs both (1) local judgments and
(2) a relation linking source elaboration to the checked Core model.
This worksheet deliberately leaves that linking theorem open.

## 1. Resource-context transitions: borrow scope and exact ownership

### 1.1 Intended judgments

The critical distinction is between an *owning* name and a *temporary
borrowed view*. A borrowed view cannot escape its lexical region, and
a borrowed owner cannot be consumed or moved during the loan.

A compact statement of the accepted borrow boundary is:

```text
     owner : T ∈ A ∪ Δ        loan(owner) = available
     Σ ; R[view ↦ borrow(owner, ρ)] ⊢ body ⇐ U ⊣ R_body ▷ Φ
     view ∉ escape(U, result, R_body)
     owner remains the same unconsumed owner in R_body
     ─────────────────────────────────────────────────────── BORROW-SCOPE (schematic)
     Σ ; R ⊢ borrow owner as view { body } ⇐ U ⊣ R' ▷ Φ
```

Here `ρ` denotes the lexical loan region and `escape(...)` is a
placeholder for the source/Core lifetime competence check. The proof
family for resource-context bindings does **not** supply a complete
definition of `escape`; the [Tour](../tutorials/tour-phase1.md#borrowing-lets-you-inspect-without-taking-ownership)
and the borrow/scope semantic contracts determine the intended rule.

At a linear consumption site, the corresponding *necessary* transition
is more direct:

```text
     x : T ∈ Δ     x is not borrowed     operation legally consumes x
     ────────────────────────────────────────────────────────── CONSUME-LINEAR (schematic)
     (Γ, A, Δ, Loans) ─consume x→ (Γ, A, Δ \ {x}, Loans)
```

A second consume of `x` cannot succeed because the required lookup no
longer holds. This is the exact behavior isolated by the Rocq
[`consumeLinear_success_exact` model](../../proof/Phil/Core/Context.v).
The normalized model does not automatically establish the correctness
of every possible surface construct or Haskell map operation.

### 1.2 Paired source examples: borrow without escape / illegal escape

**Expected accepted (Tour's complete component):**

```phil
record Inspectable mode affine {
    id : U64
}

component ReadId(item : Inspectable) provides U64 {
    let id = borrow item as view {
        return view.id;
    };
    return id;
}
```

**Expected rejected (one changed expression):**

```diff
 component ReadId(item : Inspectable) provides U64 {
     let id = borrow item as view {
-        return view.id;
+        return view;
     };
     return id;
 }
```

This attempts to return the borrowed view itself beyond its lexical
borrow region. The **loan-escape premise fails**; no proof certificate
or later assumption can make the escaped view a legal owning value.
The invalid example also cannot satisfy the public `U64` result
contract; that secondary mismatch must not obscure the borrow rule.
A future conformance negative should isolate lifetime escape in a
context where result-type mismatches do not mask the decisive diagnostic.

The `Inspectable` owner is affine, so leaving it unused after reading
the `U64` is permitted. Do **not** turn this into a general claim that
a linear owner can be silently dropped.

**Proof/implementation map.** See
[`Context.v`](../../proof/Phil/Core/Context.v),
[`ProcessJoin.v`](../../proof/Phil/Core/ProcessJoin.v),
[the Tour §3](../tutorials/tour-phase1.md#3-some-values-have-ownership-rules),
and the [borrow scope proof record](surface-borrow-view-scope-proof-v1.md).
The exact runtime/binding correspondence must be checked separately.

## 2. Session progression: legal head action, fresh successor, and close

### 2.1 Intended judgments

For an endpoint typed by its current session state, a send only
matches a send head. Successful progression consumes that precise
predecessor and installs a fresh successor carrying the continuation
session. `close` requires a terminal session state and consumes the
endpoint with **no successor**.

```text
  e : Endpoint[! (x : M).S(x)] ∈ Δ
  Σ ; R ⊢ v ⇐ M      message-admissible(v, M)
  next is fresh      owner/move checks for v succeed
  ────────────────────────────────────────────── SEND-STEP (schematic)
  R ─send v on e↦next→ R'      where e ∉ Δ' and next : Endpoint[S(v)] ∈ Δ'

  e : Endpoint[end Done] ∈ Δ     e is not borrowed
  ────────────────────────────────────────────── CLOSE-END (schematic)
  R ─close e→ R'                where e ∉ Δ' and no successor is inserted
```

The `Endpoint[...]` notation above is proof-oriented, not a copy of
Grammar v1's source spelling. For actual source forms, use the Tour's
`Client[Ping]` and `Server[Ping]` aliases.

These rules elide error/outcome-specific transport semantics; they
describe only the successful legal head transitions. They also do
not assert that independently well-typed endpoints automatically
form a compatible whole network.

The model
[`SessionStep.v`](../../proof/Phil/Core/SessionStep.v)
specifically isolates resource effects, *assuming that session-action
matching and the concrete endpoint type check happened elsewhere*.
The [Phase 0 Core judgments §8](../phase-0/semantics/core-judgments.md)
describe how owning message transfer depends on message structural mode.

### 2.2 Paired source examples: exact successor / stale endpoint

**Expected accepted (Tour's component, used in its complete Ping):**

```phil
protocol Ping {
    role Client = send (x : U8) then end Done;
    role Server = receive (x : U8) then end Done;
}

component ClientWorker(endpoint : Client[Ping], payload : U8) {
    let done = send payload on endpoint;
    close done;
}
```

**Expected rejected (same component, one changed name):**

```diff
 component ClientWorker(endpoint : Client[Ping], payload : U8) {
     let done = send payload on endpoint;
-    close done;
+    close endpoint;
 }
```

The send has already consumed the exact predecessor named
`endpoint`. The following `close endpoint` cannot typecheck as a
legal terminal close: the name is no longer available as an owning
linear endpoint, and it does not refer to the terminal successor
`done`. The unconsumed `done` is also a resource-closure problem.
These are source-invalid conditions, not runtime contingencies.

A second useful negative is:

```diff
 component ClientWorker(endpoint : Client[Ping], payload : U8) {
-    let done = send payload on endpoint;
-    close done;
+    close endpoint;
 }
```

This fails for a *different* reason: `Client[Ping]` is at a send head,
not `end Done`. This isolates **session-state mismatch** rather than
stale identity.

The successful full `LocalPing` network also requires the matching
server, role/bind connections, and terminal closure; see the next
section.

**Proof/implementation map.** See
[`SessionStep.v`](../../proof/Phil/Core/SessionStep.v),
[`Syntax.v`](../../proof/Phil/Core/Syntax.v),
[`ProtocolProjection.v`](../../proof/Phil/Core/ProtocolProjection.v),
the [Tour §§7, 18](../tutorials/tour-phase1.md#7-protocols-make-conversations-part-of-the-program),
and [concurrency safety](../../proof/Phil/Core/ConcurrencySemantics.v).

## 3. Architecture and selected-root validity: participants are not prose

### 3.1 Intended judgments

Source declarations specify an architecture; a selected program root
requires a checked finite population with explicit activation,
role assignments and binding origins. Local declaration validity and
selected-root whole-network validity are related but different.

A useful schematic rule for an **internal role** is:

```text
  role(p.r) = internal target t
  t resolves to an executable occurrence in root architecture A
  ∃! q ∈ Population(A). activation(q) = t
  role identity and binding origins match that exact p.r occurrence
  ─────────────────────────────────────────────────────── INTERNAL-ROLE (schematic)
  A ⊢ role(p.r) well-bound internally
```

The `∃!` condition here represents exactly-one applicable activation.
An ordinary role target missing or lacking activation **must reject**;
it cannot be made external by a default rule. Explicit
`role p.r = external;` has different meaning and does not itself
provide transport, boundary representation, or peer guarantees.

For the static network, one extracted necessary condition is:

```text
  Population ≠ ∅       process keys unique and nonzero
  ∀q ∈ Population. activation(key(q)) = target(q)
  ∀(key ↦ target) in activation. ∃q ∈ Population
                          with key(q)=key and target(q)=target
  ─────────────────────────────────────────────────────── STATIC-POPULATION (schematic)
  StaticPopulationValid(Population, activation)
```

This is a **presentation of the actual fields** of
[`StaticPopulationValid`](../../proof/Phil/Core/ConcurrencySemantics.v)
in Rocq, not an invented new global-checker theorem. Successful
root acceptance imposes further requirements beyond this one
predicate: exact ownership, messages, rendezvous and closure.

### 3.2 Paired source examples: full Ping / unactivated internal peer

**Expected accepted:** the entire `LocalPing` program in
[Tour §18](../tutorials/tour-phase1.md#18-how-the-ping-pieces-fit),
including:

```phil
architecture LocalPing {
    instance client = ClientWorker;
    instance server = ServerWorker;
    process client_run = client;
    process server_run = server;
    protocol ping = Ping;
    role ping.Client = client;
    role ping.Server = server;
    entry payload : U8;
    bind client.endpoint = ping.Client;
    bind client.payload = payload;
    bind server.endpoint = ping.Server;
}

program main = instantiate LocalPing;
```

Here `ClientWorker`, `ServerWorker`, and `Ping` are the exact
declarations given in the same Tour example—not imaginary implicit
imports. The linked Tour supplies the complete self-contained source,
and the Phase 1 Ping integration corpus exercises its internal path.

**Expected rejected (one deleted activation line, all other lines unchanged):**

```diff
 architecture LocalPing {
     instance client = ClientWorker;
     instance server = ServerWorker;
     process client_run = client;
-    process server_run = server;
     protocol ping = Ping;
     role ping.Client = client;
     role ping.Server = server;
     entry payload : U8;
     bind client.endpoint = ping.Client;
     bind client.payload = payload;
     bind server.endpoint = ping.Server;
 }
 program main = instantiate LocalPing;
```

The source still names `server` and assigns the internal Server
role to it. But no process activates the internal participant in the
selected root. Therefore the **internal-role activation premise**
fails. A checker must not silently create a process or reinterpret
the server as external. This is what differentiates Phil's
architecture declarations from merely decorative UML-like prose.

Another independent negative is deleting `bind client.payload = payload;`
while keeping the ClientWorker interface unchanged: an actual
runtime input would no longer have the required explicit origin.
That is not repaired by `entry payload : U8;` alone.

**Proof/implementation map.**
[ADR-024 semantics completeness](syntax-semantics-completeness-v1.md#adr-024-concurrency-extension),
[`ArchitectureInstantiation.v`](../../proof/Phil/Core/ArchitectureInstantiation.v),
[`ConcurrencySemantics.v`](../../proof/Phil/Core/ConcurrencySemantics.v),
[architecture instantiation slice](architecture-instantiation-v1.md),
and [Tour §18](../tutorials/tour-phase1.md#18-how-the-ping-pieces-fit).

Do not infer from this normalized concurrency theorem that
`ProcessKey` serialization, source-to-architecture extraction, Haskell
collections, or the physical runtime have already been proved correct.
The [concurrency proof note](concurrency-semantics-proof-v1.md)
explicitly identifies those boundaries.

## 4. Proof-scope checklist: Ethan's progress/preservation challenge

A reviewer noted that progress and preservation are a compelling
safety standard—but the safety story must carry through **each
elaboration**. This is a useful framing, with some necessary caveats.

### 4.1 Candidate statements (research agenda, *not proved here*)

For a well-defined source/Core configuration `C`, typing `⊢ C : T`,
and a small-step relation `C → C'`, typical theorems would have shapes
like:

```text
Preservation:  ⊢ C : T ∧ C → C'  ⇒  ⊢ C' : T
Progress:      ⊢ C : T         ⇒  final(C) ∨ ∃C'. C → C'
                 [possibly with separate explicit failed/stuck classifications]
```

These **illustrative** statements do not specify Phil's actual runtime
or typing relation. In particular, source semantics must distinguish
permitted explicit terminal/failure states from a stuck state.
A concurrent network can be stuck because no transition is enabled,
even when individual participants passed local safety checking.
The currently documented bounded concurrency semantics explicitly
does **not** prove deadlock freedom, fairness, or eventual response.

Progress and preservation are not sufficient, in isolation, to prove
a safe machine-code implementation or arbitrary application properties.
They depend on correct definitions of the type system, the execution
relation, and the semantics of any foreign/environmental operations.

### 4.2 Each elaboration is a separate obligation

For any translation `E : Source → Core`, a meaningful review requires
at least three distinctions:

1. **Totality / explicit rejection on supported inputs:** does `E`
   produce exactly the admitted Core object or fail when it would
   otherwise have to invent proof-relevant choices?
2. **Typing/authority preservation:** if source is accepted under
   the source judgment, is `E(source)` accepted in Core with
   corresponding resource, session, effect, and authority facts?
3. **Behavioral correspondence:** does the accepted Core execution
   model preserve the source observations and permitted failures,
   rather than merely happen to typecheck?

The Phase 1
[`Surface/Elaboration.v`](../../proof/Phil/Surface/Elaboration.v)
proves **selected** source-fragment elaboration competence with an
explicit parser boundary, not a universal refinement theorem for
all source forms. Additional elaborations—Core to Systems, Systems to
backend/target realization, proof/certificate interpretation—need
their own explicitly scoped preservation/correspondence arguments.

### 4.3 Executable evidence and open questions

When completing the consolidated Phase 1 specification:

- Define the Phase 1 *configuration*, *final/failure/stuck* classes,
  well-formed network state, and observable transition relation.
- State exactly what preservation is asserted to preserve:
  types, linear owner counts, session advancement, authority,
  effect bounds, and evidence-subject identities.
- State the conditions for progress, including blocking rendezvous
  and foreign/environment interactions; never silently assume
  a scheduler or external peer is fair.
- For every elaboration or lowering pass, name the source and target
  judgments, exact semantic translation, accepted evidence, failure
  modes, and the theorem/correspondence test that justifies it.
- Separate **verified language/kernel rules**, **implemented checker
  behavior**, and **certified compiled artifacts** in the final claims.

The present proof corpus already includes substantial modular
results; none of the questions above should be treated as an
assertion that no proof work exists.

## 5. Reviewer prompts and conformance follow-up

| Family | Positive control | Minimal negative | Primary expected rejection |
| --- | --- | --- | --- |
| Borrow scope | `ReadId` reads `view.id` and returns `U64` | replace inner result with `view` | borrowed view escapes lexical region (also public type mismatch) |
| Session identity | `ClientWorker` sends then closes `done` | close consumed `endpoint` | stale linear predecessor and unconsumed successor |
| Session head | `ClientWorker` sends then closes `done` | close initial `endpoint` immediately | `send`-head is not terminal |
| Root architecture | complete `LocalPing` | omit `process server_run = server;` | internal server role has no activated participant |
| Root input | complete `LocalPing` | omit `bind client.payload = payload;` | missing explicit runtime input origin |

These are specification-oriented counterexamples. Conformance claims
should cite actual test names and exact-commit CI results once
confirmed; until then call them **expected rejections**, not
“we executed all these negatives successfully”.

**The next pass** is to replace this worksheet's inferred
presentation predicates with a single explicitly scoped, reviewed
Phase 1 rule inventory and a theorem-to-implementation/evidence
matrix. That follow-up must be coordinated with—not substituted
for—the closeout Logic Ledger and Conformance Matrix.

---

## Context from the 2026-11-05 technical discussion

Two independent research-review observations motivated this worksheet:

- A reviewer wanted the full typing rules and operational semantics
  in one place, not merely the grammar and individual Rocq proof files.
- The same reviewer observed that progress and preservation are useful
  proof goals **only if each elaboration is also shown safe**.

A separate exchange about algebraic and higher-order effect handlers
reinforced the value of stating Phase 1's deliberately restricted
surface precisely. Algebraic effect handlers are not native Phase 1
syntax; their interaction with parallelism, linear continuations and
systems-runtime obligations remains a possible later research
question—not a missing Phase 1 commitment.

This section records the *technical questions*, not an external
endorsement or proof claim.
