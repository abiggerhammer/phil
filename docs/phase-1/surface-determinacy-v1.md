# Phase 1 Grammar-v1 concrete determinacy

Matrix case: `SURF-005`
Ledger obligation: `PHIL-SURFACE-DETERM-001`

Grammar-v1 concrete interpretation is a language-surface property, not merely a property of one recursive-descent implementation. A parser choosing one branch consistently does not establish determinacy if the normative EBNF still admits two distinct complete derivations of the same accepted source.

## Executable audit boundary

`scripts/check_phase1_surface_determinacy.py` derives nullable, FIRST, and FOLLOW facts directly from the same EBNF AST used by the canonical Grammar-v1 derivation path. `grammar/phase1-surface-determinacy.json` binds an exact SHA-256 of `grammar/phase1-surface.ebnf` and records every machine-detected local overlap together with its reviewed disposition and executable parser pressure.

The checker fails closed when the grammar digest changes, the machine-derived overlap surface changes, or a reviewed overlap loses its disposition or pressure. This intentionally makes grammar changes reopen review rather than silently inheriting an earlier ambiguity judgment.

The detector is conservative: a FIRST/FIRST or FIRST/FOLLOW overlap is a review site, not automatically a proof of ambiguity. Shared prefixes can still have one complete derivation when a later mandatory token or delimiter distinguishes the alternatives. Conversely, the Phase 1 audit found several places where parser greediness had been masking genuine ambiguity in the earlier Grammar-v1 EBNF.

## Repairs after the #451 audit

The first audit in #451 found 27 local overlap sites. It also established that four families could not be discharged merely by documenting the Haskell parser's attachment policy. #454 repairs those families in the normative grammar itself.

### Statement boundaries are explicit

Ordinary term statements now end in `;`, just like static/configuration items. Required terminators remove the earlier competition between a locally available parenthesized suffix and a following parenthesized statement. In particular, `f(x)`, `break(...)`, `continue(...)`, and failure-target argument lists cannot be split differently by statement-boundary policy.

The semicolon is required rather than optional: an optional terminator would preserve the ambiguous language.

### `using` precedes `on`

Term-level `receive_exact` and `select` place their optional evidence clause before `on`:

```text
receive_exact amount [using evidence] on endpoint
select branch [using evidence] on endpoint
```

This makes ownership structural. In nested expressions, the position of `using` identifies the expression it belongs to; there is no trailing clause that can attach to either the inner or outer command.

### Command expressions are outside arithmetic/postfix syntax

Keyword-led control/resource/protocol operations form a `command_expression` layer. `base_expression` chooses between a command and an arithmetic expression from disjoint leading-token classes. Command operands recurse through `base_expression`, so existing natural forms such as `close x + 1` retain the current interpretation `close (x + 1)`, and nested commands remain available.

A command used *inside* arithmetic or field projection must be syntactically closed with parentheses. This removes the earlier recursive competition in which the same `+`, `*`, or `.` suffix could belong either to a command's trailing operand or to an enclosing arithmetic/postfix production.

`prove` additionally uses an explicit proposition delimiter, `prove(P)`, so proposition recursion cannot leak an undelimited arithmetic/boolean tail back into term syntax.

### Dotted names and projections are factored

A bare dotted term such as `pkg.value` is a maximal `qualified_name`. Field projection becomes available after syntax that has already closed the name alternative: a parenthesized receiver, a term call, or a static-argument suffix. Examples include `(x).field`, `source().field`, and `value[T].field`.

The static-value postfix grammar uses the same principle: a bare dotted static reference is a qualified name, while projection may follow a closed static-argument suffix or a nonreference primary.

This is a grammar-level commitment, not an instruction to make `parseQualifiedName` greedy.

## What the overlap inventory means

The reviewed inventory remains useful even after the repairs. Some local overlaps are ordinary bounded lookahead sites: `provider` versus `provider implementation`, ordinary versus `boundary representation` generic requirements, tuple versus grouping, effect-set versus refinement static arguments, and comma-list/trailing-comma forms. These are retained only when the complete grammar structure distinguishes them.

A green inventory check therefore means:

1. the exact normative grammar revision is the one reviewed;
2. every machine-detected local overlap has an explicit reviewed account and executable pressure; and
3. no previously reviewed overlap has silently appeared, disappeared, or moved.

It does **not** by itself substitute for the stronger parser/grammar soundness-and-completeness correspondence obligation `PHIL-SURFACE-GRAMMAR-CORR-001`.

## Implementation pressure

The Haskell Grammar-v1 tests exercise exact located AST shape at the repaired boundaries. They distinguish qualified names from projections, preserve command-operand arithmetic, verify explicit inner/outer `using` ownership, and reject obsolete ambiguous spellings such as missing term-statement terminators, trailing evidence clauses, and undelimited `prove` propositions.

These tests are correspondence pressure for the normative grammar. The language rule comes from `grammar/phase1-surface.ebnf`, not from Haskell alternative order.

## SURF-005 closure criterion

`SURF-005` may be marked Implemented only after the repaired grammar, reviewed exact-digest overlap inventory, Haskell parser, positive corpus, and ambiguity-specific negative pressure agree on an exact green head with no known implementation-selected concrete meaning remaining.

A later mechanized unambiguity theorem can strengthen `PHIL-SURFACE-DETERM-001`; it is not legitimate to call the obligation discharged merely because one parser returns one tree.
