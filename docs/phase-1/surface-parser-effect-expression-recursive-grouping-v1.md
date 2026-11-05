# Effect-expression recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`bacf910a61786feed785de8f08fe3882ecbcdc2a`, the merge of the
[term-argument composition](surface-parser-term-arguments-recursive-grouping-v1.md).
It replaces the optional term-argument payload in an effect expression with
that slice's complete-list carrier. It records further formal evidence toward
G3 in the [implementation inventory](implementation-correspondence-inventory-v1.md).
It does not change a Logic Ledger status or the Phase 1 exit contract.

## Field replaced and structure preserved

`Phase1SurfaceEffectExpressionRecursiveGroupingSpine` stores two fields:

| Field | Representation and contract |
| --- | --- |
| Static reference | The existing `Phase1SurfaceStaticReferenceSpine`, preserving the complete qualified name and its retained optional static-argument tree |
| Optional term arguments | `option Phase1SurfaceTermArgumentsRecursiveGroupingSpine`, replacing every expression in a present argument list |

The record stores the new child carrier directly, without a duplicate old
effect value or input tree. Its argument field distinguishes `None`, meaning
absent term arguments, from `Some` of an empty list, meaning present `()`.
A present nonempty list carries every expression, including its independent
main and reject-fallback fields, in the original order.

The static-reference representation is preserved at its existing scope. Its
decoder checks the qualified-name structure and the optional `static_arguments`
named wrapper while retaining that subtree's interior. This slice does not add
full static-argument validation or replace static-reference argument payloads.

## Executable entry points and proof contracts

| Entry point | Input |
| --- | --- |
| `phase1_surface_normalize_optional_term_arguments_recursive_grouping` | The shallow optional term-argument tree |
| `phase1_surface_normalize_effect_expression_recursive_grouping_spine` | The existing shallow effect-expression carrier |
| `phase1_surface_normalize_effect_expression_recursive_grouping_tree` | A raw `effect_expression` parse tree |
| `phase1_surface_refine_effect_expression_recursive_grouping` | The existing full shift-refined effect-expression carrier |

The optional normalizer maps the new raw term-arguments normalizer over a
present payload. Its reconstruction theorem states that mapping the new
term-arguments erasure over the resulting option yields the exact old option.
That equality preserves presence as well as the entire present tree. Successful
normalization of absent arguments returns `Some None`; failure remains the
distinct outer `None` result.

The shell theorem reconstructs the exact old `Phase1SurfaceEffectExpressionSpine`,
including its complete static-reference carrier. The raw normalizer composes
the existing two-field effect decoder with this conversion and reconstructs
the complete original tree on success.

The legacy adapter takes
`Phase1SurfaceEffectExpressionExpressionFallbackBaseChoiceShiftRefinedSpine`.
It copies the existing static-reference field directly and maps the new
term-arguments legacy adapter over the optional argument value. Alongside exact
tree reconstruction, a separate theorem proves equality of the complete
static-reference carrier. It does not re-decode that reference or require the
old value to have come from a particular normalizer.

The totality companion extracts the optional `term_arguments` derivation from
the canonical `effect_expression` sequence. Absence is immediate; presence
supplies the child's derivation to the preceding slice's raw or legacy totality.
The public shell, raw-tree, and legacy-adapter totalities require only the
relevant `Derives` judgment. There is no caller-supplied fuel, shared fuel
witness, or successful-child-normalization premise.

These are grammar-structural results. Grammar validity comes from the derivation
certificate. Exact reconstruction and reference-field preservation alone do
not certify arbitrary hand-built values, typing, effect semantics, source-byte
lexing, or production AST behavior.

## Sources and replay evidence

| Module | Evidence |
| --- | --- |
| [GrammarAstEffectExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstEffectExpressionRecursiveGroupingSpine.v) | Carrier, optional/shell/raw conversion, direct legacy adapter, exact reconstruction, and reference preservation |
| [GrammarAstEffectExpressionRecursiveGroupingSpineTotality.v](../../proof/Phil/Surface/GrammarAstEffectExpressionRecursiveGroupingSpineTotality.v) | Derivation-only totality for optional payloads and all public entry points |
| [GrammarAstEffectExpressionRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstEffectExpressionRecursiveGroupingExamples.v) | Fourteen checked integration and rejection controls |

The examples use a dotted effect name with present `[Unit]` static arguments.
They derive canonical absent, present-empty, and present-nonempty effects from
the grammar and inspect the option constructors directly. The nonempty fixture
reuses the preceding slice's three distinct arguments, including its later
reject fallback and nontrivial retained command/failure-target payload. Controls
inspect the complete reference carrier, all present arguments, and exact tree
reconstruction. Legacy controls exercise all three argument-presence cases.

The existing mixed term-arguments derivation is reused at its new child path
through a local mutual path-transport lemma for ordinary `Derives`. This does
not assert path invariance for oracle-resolved semantics or change the grammar.
Negative controls reject a malformed later reject operand, an unwrapped second
child, a present node with the wrong name, and malformed present parentheses.
Node-count fuel in the old-decoder fixture is only a concrete compatibility
control, not a universal bound for that decoder. The new entry points have no
fuel parameter.

The [source-spine workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
retains its prior targets and adds all three new modules under Rocq 9.2.0.
It checks forty-two configured theorem assumptions for closure under the global
context and runs the full recursive compiled-proof checker over eighteen
configured totality/example endpoints and their dependencies. The accumulated
artifact contains sixty-six files and sixty-nine recorded identities, including
all three new source/object pairs.

Six existing effect-expression prerequisite modules receive direct-owner import
and proof-script repairs. Their definitions and theorem statements remain
unchanged. The new proof route uses the shallow effect totality and the new
term-arguments totalities; no old full shared-fuel totality/support chain is
imported. The shallow effect module also drops its unused effect-set dependency
in favor of the helpers' direct owners.

## Remaining composition boundaries

The next consumer is the ordered list in an effect-set literal. Its lift must
replace every effect expression while preserving empty `{}`, commas, order,
and the enclosing literal/reference alternative. The subsequent route proceeds
through the `effects ... within ...` generic-requirement alternative, optional
requirement lists in record/data declarations, and the corresponding retained
implementation-representation field. This route does not cover every generic
requirement or declaration body.

Static-reference argument interiors, named-postfix argument payloads, command
bodies, failure-target arguments, and the generic grouping expression's nested
fallback boundary retain their existing representations. Faithful production
AST binding, source-byte lexing, and the finite implementation-interface coverage
contract remain separate obligations. This slice does not close G2 or G4 or
promote an umbrella target.
