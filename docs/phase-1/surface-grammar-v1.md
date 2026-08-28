# Phase 1 Surface Grammar v1

## Status and authority

`grammar/phase1-surface.ebnf` is the canonical concrete-syntax authority for the Phil Phase 1 surface language.

The grammar fixes what token sequences constitute Phase 1 surface syntax. It does **not** make syntactic acceptance semantic acceptance. Declaration checking, identity, authority, resource/session legality, assurance, and lowering remain governed by their checked semantic contracts.

> **The grammar determines what can be parsed; the checker determines what it means and whether it is admissible.**

The current Haskell `Phil.Surface.Parser` began as the Phase 0 parser and is not made normative by this decision. Phase 1 parser work must establish correspondence to the canonical grammar rather than treating implementation behavior as specification.

## One source of truth

The canonical EBNF is deliberately not duplicated by a hand-maintained Rocq grammar. `scripts/derive_phase1_surface_grammar.py --write` derives the proof-facing Rocq EBNF syntax tree, rule set, start symbol, reserved keywords, and canonical EBNF SHA-256. CI derives it twice for determinism and compiles the generated Rocq artifact.

## Surface completeness criterion

Grammar v1 is required to expose every **source-author-controlled semantic choice** admitted by the stabilized Phase 1 semantic contracts. It is not required to expose deterministic elaboration products, assurance/build artifacts, or target/internal realization state.

The detailed classification and audit are recorded in `syntax-semantics-completeness-v1.md`. In short:

- if a programmer may choose it as part of ordinary Phil source semantics, Grammar v1 needs a spelling;
- if the checker derives it canonically, another spelling would create a false choice;
- if it is proof/qualification/admission metadata, ordinary source may depend on it but may not self-assert it;
- if it belongs to Systems/target realization or compiler/runtime bookkeeping, it is not source syntax.

This is why Grammar v1 exposes explicit transport, outcome class, residual obligations, join/loop contracts, authority requirements, exact static contract references, and ADR-024 process activation sites, but does not expose `PendingRecv`, provider-qualification evidence records, scheduler/thread identities, `StageContract`, or backend ABI objects as user-authored terms.

## Canonical lexical and structural choices

The EBNF header owns the lexical contract: Unicode whitespace and `//` comments are trivia; identifiers use the stated Unicode identifier class; decimal integers are ASCII digits; `U<digits>` is a syntactic unsigned-width type token; strings use the small explicit escape set; and parsing consumes the entire file.

Phase 1 v1 uses `[...]` for static/generic parameters and arguments and `(...)` for runtime arguments/products. Static declaration/configuration items use semicolon terminators; ordinary term statements retain the Phase 0 semicolon-free style.

Attributes use `@name("value")`. Records, sums, aliases, claims, callable contracts, functions, providers, protocols, capabilities, boundary representations, architectures, components, and program roots are all ordinary top-level declaration forms. Architecture occurrence creation uses `instance`; deliberate sharing uses `ref`; static process activation uses `process`; a program root says `program ... = instantiate ...`.

## Static arguments, contracts, and requirements

The static parameter telescope includes the bounded Phase 1 kinds `Type`, `Nat`, `Session`, `Message`, `Effects`, and exact provider/callable/boundary/architecture contract kinds.

A static actual may therefore be a type, a session description/reference, an ordinary static expression, or an effect-set literal as demanded by the expected parameter kind. This matters for forms such as:

```phil
type WordBox = Box[U32];

protocol Wrapper[S : Session] {
  role left = S;
  role right = S;
}
```

Kind checking is semantic. The parser does not decide whether one ambiguous-looking static form inhabits the expected kind.

Contract-bearing positions use `static_reference`, not merely a bare name, where the semantic contract may itself be specialized. Thus a boundary may say `receive using Decoder[T];`, a protocol transition may say `using FrameCodec[Message]`, and a claim application may name an exact generic claim family.

The explicit public generic requirement block preserves the admitted requirement categories rather than collapsing them:

```phil
requires {
  structural T : duplicate;
  proposition Ordered(x);
  provider P : BlobProvider;
  callable F : Reader;
  boundary B : Wire;
  architecture A : StorageArchitecture;
  effects E within { storage.Read(store) };
  authority BlobRead;
  boundary representation WireRep;
  representation HostIndependent(T);
  placement SameDomain(x, y);
  cost BoundedCost(x);
  environment StableClock;
}
```

The exact semantic identity, admissibility, evidence, and discharge path of each requirement remain checker/assurance responsibilities.

## Structural mode syntax

Structural mode is a checked property of the value type/resource contract. Ordinary owning bindings inherit `mode(T)` and do not carry binder-local `linear`/`affine` qualifiers.

Transparent records and sums derive a minimum mode from owned contents. A nominal declaration may explicitly strengthen it with `mode unrestricted|affine|linear`; checking requires the declaration not to weaken the derived minimum. Capabilities state possession mode explicitly because authority and copy/drop discipline are distinct semantic facts. Transparent aliases inherit the target mode.

Closures normally derive their minimum mode from owned captures. Where the callable/lifecycle contract intentionally makes the callable value stricter than that minimum, Grammar v1 also permits:

```phil
closure mode linear (x : U32) satisfies OneShot { ... }
```

The explicit closure mode may not weaken capture-derived mode and does not by itself prove one-shot invocation behavior; callee transition semantics remains separate.

## Types, refinement, products, and transport

Refinement types use `{x : T | P}`. Finite membership and disjointness use infix `in` and `disjoint`. Non-definitional transport is explicit:

```phil
transport payload to Bytes[n] using length_equal
```

`accept value as T` remains distinct: it asks ordinary checking/refinement machinery to establish `T`; it is not evidence-bearing transport.

Ordinary finite products are source-expressible. Product types use two or more comma-separated elements:

```phil
(U32, Bool)
(U32, Bool, ContentId)
```

Tuple values use the same arity rule:

```phil
(1, true)
(id, payload, proof)
```

A single parenthesized expression `(x)` is grouping, not a one-element tuple. Tuple patterns continue to destructure products. Product structural mode follows owned contents under ordinary resource rules.

## Effect syntax

Source-level may-effects are explicit semantic labels, optionally indexed by semantic term arguments. Effect sets can be literals or named effect-set parameters. A generic `Effects` parameter may be bounded with `effects E within ...;`.

Backend calls, copies, staging operations, synchronization, or other target-introduced work do not become source effects merely because they execute. Their additional effects belong to realization/StageContract accounting.

## Callable outcomes, obligations, and callee transitions

Callable outcome class is source semantic information. Grammar v1 does not permit a plain unclassified outcome set because ADR-005 distinguishes successful continuation, typed-negative recoverable control, declared terminal completion, and fatal failure.

Canonical spelling is:

```phil
outcomes {
  success Stored,
  negative StoreFailure,
  terminal Closed,
  fatal Crashed
};
```

A branch-sensitive residue repeats the class:

```phil
outcome negative StoreFailure {
  state (x : OwnedBytes[n]);
  obligation RetryPolicy(x);
  callee preserve;
}
```

`state (...)` is the checked result/resource telescope for that outcome. `ensures P;` states a guarantee established by the outcome. `obligation P;` states a residual obligation that remains live at that boundary. `assumes P;` remains a conditional dependency on the callable contract, not a residual obligation and not a proof.

Callable-wide residual obligations may likewise be declared with `obligation P;`.

Callee transition spelling is `preserve`, `consume`, or `replace with ExactSuccessor[args...] [state e]`. Outcome-specific callee residue is allowed where invocation behavior differs by branch.

Parsing does not decide whether outcome classifications, state residues, obligations, or callee transitions are mutually consistent. Those are callable/resource/failure/assurance checks.

## Protocol choice and static session syntax

Protocol families remain binary in the Phase 1 executable profile. Session syntax includes send/receive/select/offer/end/guarded recursion and `continue`. A role-local session may also be an exact static session reference, enabling ordinary abstraction over `S : Session`.

Term-level `offer` is present alongside `select`, `send`, `receive`, and `close`. The exact protocol instance, role, state, branch set, guard evidence, and endpoint succession remain semantic checks.

## Control-state contracts

Join and loop syntax now exposes the state facts already admitted by the resource/control semantics.

A join may state both its post-join state telescope and invariant:

```phil
if cond join state (x : T, y : U) invariant Compatible(x, y) {
  ...
} else {
  ...
}
```

The state telescope does not manufacture owners or evidence; every continuing predecessor must project into it through the ordinary checked join relation.

Loop state may carry explicit dependent types together with initial values:

```phil
loop state (i : U32 = start, owner : OwnedBytes[n] = bytes)
     invariant Valid(i, owner) {
  ...
  continue (i_next, owner_next)
}
```

Initial entry and every `continue` edge must re-establish the same loop-state contract. Untyped `x = e` remains available when the exact state type is unambiguously inferred.

Typed-negative control is also a first-class expression:

```phil
reject reason
```

This is distinct from fatal `fail FailureClass(...) on live_resource`, which performs the declared fatal resource transition. The existing `e or reject reason` fallback remains an ergonomic exhaustive-control form over a declared negative result.

## Boundary, architecture, and static process syntax

Boundary declarations expose direction-specific receive/send roles, correspondence, canonicality, failure types, and laws. Recognition, validation, encoding, and protocol boundary use may name specialized exact static contracts.

Architecture declarations expose author-controlled source semantics: occurrence creation/references, provider/protocol/role/boundary bindings, authority origins and grants, entries, assumptions, exported obligations, observables, constraints, and ADR-024 process activation sites.

A bounded Phase 1 process site is written:

```phil
architecture Pair {
  instance left = Worker;
  instance right = Worker;
  process left_run = left;
  process right_run = right;
}
```

The right-hand side is deliberately a `qualified_name`, not a `static_reference`: `process` refers to an already-created executable architecture occurrence and creates stable process/activation identity; it does not instantiate or clone that target. Process population, target executability, exactly-once activation, ownership partition, protocol-role/process binding, rendezvous, terminal closure, and ProcessKey identity are semantic checks under ADR-024.

There is no term-level process expression in Phase 1. Thread/task/PID/worker identity, scheduling, buffering, locks/atomics, execution placement, cancellation machinery, and other physical concurrency choices remain Systems/StageContract realization facts rather than source syntax.

Concrete provider admission, target/ABI selection, runtime-site binding, carrier choice, and StageContract construction remain later competent-layer decisions, not architecture-source syntax.

## Semantic rejection remains competent

The grammar intentionally parses forms whose legality depends on semantic information. Examples include static-argument kind, supported integer width, structural-mode strengthening, refinement sort correctness, transport evidence competence, finite-collection sorts, outcome-set/residue consistency, residual-obligation disposition, exact replacement-callee compatibility, session duality, provider refinement, authority possession, join/loop state projection, architecture binding validity, process target validity, process ownership partition, and process activation closure.

Malformed syntax is rejected by the parser. Semantically illegal but well-formed syntax is rejected by the competent semantic checker.

## Production corpus

`test/fixtures/phase1-surface/manifest.json` is the declarative parser-production corpus. Positive fixtures assert whole-file syntactic acceptance only; negative fixtures are malformed forms that must fail at the syntax layer. `surface-parser-production-corpus-v1.md` describes its integration contract.

The broader semantic-to-surface audit that motivated the previous cases is recorded in `syntax-semantics-completeness-v1.md`. ADR-024 extends that completeness boundary with one new author-controlled architecture choice, protected by the process-production corpus cases; scheduler/realization choices remain deliberately non-surface.

## Versioning

“v1” names this Phase 1 concrete-syntax epoch. Git history and the embedded EBNF SHA-256 identify exact revisions inside the epoch. Deliberate Phase 1 reconciliations may extend the epoch before the canonical source front end is frozen; every such change invalidates parser-conformance evidence tied to the prior grammar digest.

The earlier reconciliation sequence exposed already-admitted semantics: refinement/transport/finite relations/outcome residues/offer; declaration-level structural modes; and the broader static-actual/requirement/product/outcome-class/obligation/control-state completeness repairs. ADR-024 is a deliberate bounded Phase 1 semantic extension: it adds only the architecture-level `process` activation form while keeping physical concurrency mechanisms outside source semantics.

A future incompatible syntax change must be explicit rather than silently changing parser behavior.

## Deliberate non-goals

Grammar v1 does not define semantic elaboration, a formatter, target/backend syntax, dynamic process creation, term-level spawn/await, futures/race combinators, shared-memory synchronization/atomics, asynchronous mailboxes, multiparty protocol semantics, implicit cancellation/supervision, scheduler-control syntax, macros/general compile-time metaprogramming, user-written quantifiers/unrestricted existentials, arbitrary type-level computation, proof/certificate formats, provider qualification artifacts, StageContract syntax, or proof that the current Haskell parser already implements every production.
