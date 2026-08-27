# Phase 1 Surface Grammar v1

## Status and authority

`grammar/phase1-surface.ebnf` is the canonical concrete-syntax authority for the Phil Phase 1 surface language.

The grammar fixes what token sequences constitute Phase 1 surface syntax. It does **not** make syntactic acceptance semantic acceptance. Declaration checking, identity, authority, resource/session legality, assurance, and lowering remain governed by their checked semantic contracts.

In particular:

> **The grammar determines what can be parsed; the checker determines what it means and whether it is admissible.**

The current Haskell `Phil.Surface.Parser` began as the Phase 0 parser and is not made normative by this decision. Phase 1 parser work must establish correspondence to the canonical grammar rather than treating implementation behavior as specification.

## One source of truth

The canonical EBNF is deliberately not duplicated by a hand-maintained Rocq grammar.

Run:

```sh
python3 scripts/derive_phase1_surface_grammar.py --write
```

to derive `proof/Phil/Surface/Grammar.v`. The generated file is ignored by Git. It contains:

- a typed Rocq EBNF syntax tree;
- the exact grammar rule set;
- the start symbol `source_file`;
- the reserved keyword set derived from literal grammar terminals; and
- the SHA-256 digest of the canonical EBNF source.

CI derives the Rocq artifact from a clean checkout, derives it a second time to check determinism, and asks Rocq to compile the result. Thus the proof-facing grammar is mechanically downstream of the EBNF instead of being a second editable specification.

## Canonical lexical rules

The EBNF header owns the lexical contract. In summary:

- Unicode whitespace and `//` line comments are trivia between tokens;
- identifiers begin with a Unicode letter or `_` and continue with Unicode alphanumerics, `_`, or `'`;
- identifiers exclude the keyword literals appearing in the grammar;
- decimal integer syntax is ASCII decimal digits;
- `U` followed by decimal digits is a syntactic unsigned-width type token, while supported widths are checked semantically;
- string literals are UTF-8 double-quoted strings with the small escape set stated in the grammar; and
- parsing consumes the entire source file.

Keyword and `U<digits>` recognition take precedence over ordinary identifiers.

## Canonical structural choices

Phase 1 v1 fixes the following surface conventions:

- a source file has an optional `module`, then imports, then declarations;
- module/import and static declaration/configuration items use semicolon terminators;
- ordinary term statements retain the semicolon-free Phase 0 style;
- generic/static parameters use `[...]`; runtime parameters and arguments use `(...)`;
- generic requirements use an explicit `requires { ... }` block;
- generic effect-set parameters use the `Effects` kind and may be bounded by an `effects E within ...;` requirement;
- callable contracts state latent may-effects with an `effects ...;` clause;
- callable contracts may state branch-sensitive resource/callee postconditions with `outcome T { ... }` blocks;
- callee replacement names its exact successor contract with `replace with ...`, plus an explicit state expression where required;
- refinement types use `{x : T | P}`;
- non-definitional equality transport uses `transport value to T using evidence`;
- native finite-collection relations use infix `in` and `disjoint` propositions;
- attributes use `@name("value")`, including semantic-key annotations such as `@key(...)` and `@instance_key(...)` when admitted by the semantic checker;
- records, sums, aliases, claims, callable contracts, functions, providers, protocols, capabilities, boundary representations, architectures, components, and program roots are all ordinary top-level declaration forms;
- the Phase 1 protocol surface is explicitly binary: a protocol declaration contains exactly two role-local session declarations; distinct role names and duality remain semantic checks;
- architecture occurrence creation uses `instance`; deliberate sharing uses `ref`;
- a program root explicitly says `program ... = instantiate ...`;
- expression and proposition precedence are fixed by the grammar rather than parser implementation order;
- Phase 0 boundary/session term forms remain syntactically available, including term-level `offer`, while Phase 1 adds functions/closures, records/sums, `if`, `match`, explicit join-state annotations, and loop state/invariants.

These choices freeze spelling and punctuation for Phase 1 v1. They do not freeze a formatter or whitespace layout policy.

## Refinement, relation, and transport syntax

Grammar v1 exposes the bounded dependent/refinement machinery already admitted by Phil Core without making the parser a proof engine.

A refinement type binds one value in one proposition:

```phil
{x : U32 | x <= limit}
{payload : Bytes[n] | DigestMatches(id, payload)}
```

The binder scope is the proposition inside the same refinement type. Sort checking, definitional equality, structural/resource legality, and proposition discharge remain semantic checks.

Finite membership and disjointness are native proposition relations:

```phil
candidate in allowed
left disjoint right
```

They are not syntax sugar for opaque claim declarations. The checker establishes whether the operands have compatible finite-collection sorts.

When two types/indices/subjects are not definitionally equal, a source program may explicitly choose a checked transport:

```phil
transport payload to Bytes[n] using length_equal
```

The `using` expression must supply evidence competent for the exact required equality or transport relation. No symmetry, subject retargeting, succession relation, or proof competence is inferred by parsing.

`accept value as T` remains a separate operation: it asks ordinary checking/refinement machinery to establish `T`; it is not a substitute for evidence-bearing non-definitional transport.

## Effect syntax

Grammar v1 represents source-level may-effects explicitly without committing Phil to algebraic effect handlers or a target-runtime effect language.

An effect label is a qualified name optionally applied to term arguments. This permits both unindexed labels and semantic-subject-indexed labels:

```phil
effects { log.Flush, storage.Write(blob_store), network.Send(endpoint) };
```

An effect set may also be named by a generic/static effect-set parameter:

```phil
callable Forward[E : Effects](x : Bytes[n]) -> Unit {
  effects E;
}
```

A generic requirement may place an upper bound on such a parameter:

```phil
requires {
  effects E within { storage.Read(source), storage.Write(destination) };
}
```

`within` is syntax for a semantic subeffect bound: the checker, not the parser, determines effect identity, subject identity, set inclusion, and whether an effect is legal in the surrounding contract. Effect-set literals may also appear as static arguments where the expected generic kind is `Effects`; ordinary generic-kind checking remains semantic.

This is deliberately source-semantic syntax. Backend calls, copies, staging operations, or other target-introduced machinery do not become source effects merely because they execute. Their additional effects belong to realization/StageContract accounting.

## Callable outcomes and callee transitions

`outcomes { ... };` names the public callable outcome/failure set. When the resource or callable residue differs by outcome, Grammar v1 exposes that branch sensitivity directly:

```phil
callable Store(x : OwnedBytes[n]) -> Result {
  outcomes { Stored, StoreFailure };

  outcome Stored {
    state (id : ContentId);
    callee preserve;
    ensures StoredAt(id);
  }

  outcome StoreFailure {
    state (x : OwnedBytes[n]);
    callee preserve;
  }
}
```

`state (...)` is a checked post-outcome telescope. Parsing does not decide structural modes, stable-subject continuity, succession evidence, or whether the state is legal for that outcome. An outcome-residue block must correspond to the stabilized public outcome set; duplicate, missing, or contradictory semantic facts remain checker errors.

Callee replacement is exact rather than nominal:

```phil
callee replace with NextCallable[args...] state next_state;
```

The state suffix is optional when the successor contract does not carry a distinct state index. `callee preserve;` and `callee consume;` remain the other two canonical forms. The same transition syntax may occur inside an outcome block when callable ownership differs by public outcome.

## Protocol choice terms

Session declarations already distinguish internal `select` from external `offer`. Grammar v1 also includes the corresponding term forms. The canonical external-choice term is:

```phil
offer endpoint {
  Payload(x) => { ... }
  Cancel => { ... }
}
```

The branch set, payload binders, exact protocol instance/role/session state, guard evidence, and endpoint succession are semantic checks. This restores a Phase 0 surface operation that had been accidentally omitted from the first canonical EBNF even though the semantic operation and parser support already existed.

## Semantic rejection remains competent

The grammar intentionally accepts some forms whose legality depends on semantic information. Examples include whether a named static argument denotes a type or value in the expected parameter position, whether an unsigned width is supported, whether a refinement proposition is sort-correct, whether transport evidence proves the exact required relation, whether finite-collection relation operands have compatible sorts, whether a callable outcome residue matches the public outcome contract, whether a replacement callee names a compatible exact successor, whether a protocol's two roles are distinct and dual, whether a provider implementation satisfies its exact contract revision, and whether a target-independent architecture binding is valid.

Those cases belong to elaboration/checking, not to ad hoc parser rejection. Conversely, malformed concrete syntax is rejected by the parser before semantic checking begins.

## Versioning

“v1” names this Phase 1 concrete-syntax epoch. Git history and the embedded source SHA-256 identify exact grammar revisions within it. The epoch may still receive deliberate Phase 1 revisions before the canonical source front end is frozen; each such revision changes the exact grammar digest and therefore the identity to which parser-conformance evidence must bind.

The type-system reconciliation revision adds refinement types, explicit transport, native finite membership/disjointness, branch-sensitive callable outcome residues, exact replacement-callee syntax, and the previously omitted term-level `offer`. These are surface realizations of already-admitted semantics rather than a new semantic epoch.

A future incompatible concrete-syntax change must be explicit rather than silently changing parser behavior. Whether such a change becomes a new Phase 1 grammar revision or a later language-surface version is a compatibility decision, not parser discretion.

## Deliberate non-goals

This grammar does not define:

- semantic elaboration or Core meaning;
- a formatter or canonical whitespace style;
- target/backend syntax or target realization;
- multiparty/asynchronous protocol semantics;
- macro systems or arbitrary compile-time metaprogramming;
- user-written quantifiers, unrestricted existentials, or arbitrary type-level computation; or
- proof that the current Haskell parser already implements all Phase 1 productions.

Parser/grammar correspondence is an implementation and assurance obligation to discharge as the Phase 1 front end catches up with the now-canonical surface.
