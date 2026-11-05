# Term-argument recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`bbfdfa9f19c3da4b52c248e6d80223d872bfbe84`, the merge of the
[expression composition](surface-parser-expression-recursive-grouping-v1.md).
It replaces every expression payload in a term-argument list with that slice's
recursive grouping expression carrier. It records further formal evidence
toward G3 in the [implementation inventory](implementation-correspondence-inventory-v1.md).
It does not change a Logic Ledger status or the Phase 1 exit contract.

## Field replaced

`Phase1SurfaceTermArgumentsRecursiveGroupingSpine` stores a list of
`Phase1SurfaceExpressionRecursiveGroupingSpine` values. Every list position
therefore carries the new main-base and optional-fallback representation,
including the independently refined base of a reject fallback. The record
stores no predecessor list or duplicate original parse tree.

The empty list represents the present `term_arguments` syntax `()`. An absent
optional argument payload is a different case in an enclosing consumer; it is
not represented by this record's empty list. A nonempty list reconstructs its
first expression and every following comma/expression pair, in order, between
the original parentheses. Grammar-v1 does not admit a trailing comma here.

## Executable entry points and proof contracts

| Entry point | Input |
| --- | --- |
| `phase1_surface_normalize_term_argument_recursive_grouping_values` | A list of expression parse trees |
| `phase1_surface_normalize_term_arguments_recursive_grouping_spine` | The existing shallow term-arguments carrier |
| `phase1_surface_normalize_term_arguments_recursive_grouping_tree` | A raw `term_arguments` parse tree |
| `phase1_surface_refine_term_arguments_recursive_grouping` | The existing full shift-refined term-arguments carrier |

The list conversion invokes the new expression raw normalizer on every element.
The raw term-arguments normalizer first uses the existing shallow shell decoder,
which checks the parentheses, optional first/rest shape, comma pairs, and list
structure. The compatibility adapter normalizes the exact erasure of an old
`Phase1SurfaceTermArgumentsExpressionFallbackBaseChoiceShiftRefinedSpine` value.

The central reconstruction theorem states that, whenever list conversion
succeeds,

```coq
map phase1_surface_expression_recursive_grouping_spine_tree refined = arguments
```

This equality preserves the complete argument list, including its length,
order, and every element. The shell theorem reconstructs the exact predecessor
carrier. The raw and compatibility theorems reconstruct the entire input tree,
including its punctuation and empty/nonempty shape.

The companion totality proof obtains each expression's canonical `Derives`
judgment from the `term_arguments` derivation. It handles the empty optional
entry directly and proves the repeated comma/expression suffix by induction.
Every child conversion then follows from expression totality. The public
shell, raw-tree, and compatibility totalities require only the relevant grammar
derivation; they require no caller-supplied fuel, shared fuel witness, or
successful-child-normalization premise. The compatibility theorem does not
require the old value to have been produced by a particular normalizer.

These are grammar-structural results. A derivation supplies grammar validity;
exact reconstruction alone does not certify arbitrary hand-built carrier
values, typing, evaluation, source-byte lexing, or production AST behavior.

## Sources and replay evidence

| Module | Evidence |
| --- | --- |
| [GrammarAstTermArgumentsRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstTermArgumentsRecursiveGroupingSpine.v) | Carrier, list/shell/raw conversion, legacy adapter, and exact reconstruction |
| [GrammarAstTermArgumentsRecursiveGroupingSpineTotality.v](../../proof/Phil/Surface/GrammarAstTermArgumentsRecursiveGroupingSpineTotality.v) | Grammar-derived totality for all list positions and the public entry points |
| [GrammarAstTermArgumentsRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstTermArgumentsRecursiveGroupingExamples.v) | Thirteen checked integration and rejection controls |

The examples include grammar-derived empty and three-element lists, a singleton
with independent main and reject operands, exact complete-list reconstruction,
and the old full-carrier adapter. The three arguments are deliberately distinct:
the first contains seven negations and seven groups without a fallback, the
middle retains a command and a failure target with nontrivial grouped arguments,
and the last has a multi-operator main operand and a distinct reject operand
with seven negations and seven groups. Typed-field
checks inspect all three positions, so a skipped, copied, swapped, or truncated
element cannot satisfy the control. The retained failure-target payload is
checked for exact preservation, not refinement of its interior.

Negative controls reject a malformed main expression in the middle position,
a malformed reject operand in the final position, a wrong separator, a trailing
comma without an expression, and a wrong closing delimiter. The legacy adapter
fixture supplies node-count fuel to the old decoder as a concrete control;
it makes no universal sufficient-fuel claim for that old decoder. The new
entry points have no fuel parameter.

The [source-spine workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
retains its prior targets and adds all three new modules under Rocq 9.2.0.
It checks thirty-seven configured theorem assumptions for closure under the
global context and runs the full recursive compiled-proof checker over the
accumulated totalities and examples, including their dependencies. The artifact
includes the new source/object pairs, producing sixty files and sixty-three
recorded source/object identities across the accumulated evidence.

Three existing term-argument prerequisite modules receive direct-owner import
and proof-script repairs. Their definitions and theorem statements remain
unchanged. The new totality proof uses the shallow term-arguments totality and
the new expression totality; it does not import the old full shared-fuel
term-argument totality/support chain.

## Remaining composition boundaries

This completes the selected outer term-argument list lift. The next consumer
is the optional argument field in the effect-expression carrier. Its conversion
must distinguish absent arguments from present empty `()` arguments while
preserving the static reference. The established route then proceeds through
every effect-set literal element, the `effects ... within ...` generic-requirement
alternative, optional requirement lists in record/data declarations, and the
corresponding retained implementation-representation field. This route does not
cover every generic requirement or declaration body.

Named-postfix static and term arguments remain separate consumers of their
preceding representations. Command bodies and failure-target arguments remain
exact retained trees. The generic recursive-grouping expression type used
inside parenthesized/tuple children still has its own retained fallback tree
boundary and generic structural forms. Updating this outer list does not
silently replace any of those recursive fields.

Faithful production AST binding, source-byte lexing, and the finite
implementation-interface coverage contract remain separate obligations.
This slice does not close G2 or G4 or promote an umbrella target.
