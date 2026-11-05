# Arithmetic recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`a611f3d4c42647c1eb31831746b582078b14b900`, the merge of the
[primary/postfix composition](surface-parser-primary-postfix-recursive-grouping-v1.md).
It carries that replacement through the ordinary unary and arithmetic
precedence carriers. It records formal evidence toward G3 in the
[implementation-correspondence inventory](implementation-correspondence-inventory-v1.md);
it does not change a Logic Ledger status or the Phase 1 exit contract.

## Fields replaced

The new carriers consume the preceding slice's postfix representation in every
operand position:

| Layer | Recursive grouping payload | Structure preserved |
| --- | --- | --- |
| Unary | A new postfix leaf beneath any number of recursive negation constructors | Every unary negation and the exact postfix tree |
| Multiplicative | Leading unary operand and the right operand of every suffix | `*`, `/`, `%`, suffix count, and original order |
| Additive | Leading multiplicative operand and the right operand of every suffix | `+`, `-`, suffix count, and original order |
| Shift | Leading additive operand and the right operand of every suffix | `<<`, `>>`, suffix count, and original order |

Each suffix uses the established operator enum. The replacement records store
typed child carriers; reconstruction functions compute their old shallow views.
No predecessor carrier or duplicate original tree is stored beside the new
representation.

This is a structural translation. The operator sequence is preserved without
evaluating it, assigning types to its operands, or proving arithmetic laws.

## Executable entry points and proof contracts

Each layer has a raw-tree entry point named
`phase1_surface_normalize_<layer>_expression_recursive_grouping_tree` and an
adapter named `phase1_surface_refine_<layer>_expression_recursive_grouping`.
The layer names are `unary`, `multiplicative`, `additive`, and `shift`.

The public results establish:

1. **Exact reconstruction on success.** A returned carrier reconstructs the
   identical input parse tree. This implication applies to arbitrary input
   trees, without requiring a derivation as an additional premise.
2. **Totality from a grammar derivation.** A canonical Grammar-v1 derivation of
   the corresponding nonterminal supplies a successful normalization result
   with exact reconstruction. Callers supply no normalization-success premise
   and do not choose fuel.
3. **Compatibility with existing typed carriers.** If an old carrier's erasure
   has the corresponding grammar derivation, its adapter succeeds and preserves
   that erasure. The theorem does not require the old value to have been
   produced by a particular normalizer.

Grammar validity is supplied by the derivation certificate. Exact reconstruction
alone does not validate arbitrary input trees or hand-built carrier values.

For multiplicative, additive, and shift expressions, the intermediate shell
theorems prove equality of the reconstructed shallow carrier itself. The suffix
list theorem proves that mapping the reconstruction over the entire converted
list returns the original list. This includes every operator and right operand
at its original position.

The raw arithmetic normalizers reuse the existing shallow decoders. Their
totality proofs extract the leading child derivation and every suffix child
derivation from the canonical sequence and repetition judgments, then invoke
the lower layer's proved total normalizer. The old fully refined arithmetic
adapters normalize their erasures through that same executable path.

## Concrete termination and fuel

The unary adapter recurses structurally over the old recursive unary carrier.
It needs no fuel argument and invokes the preceding postfix adapter at a leaf.

The raw unary decoder recurses through negation using
`phase1_surface_grouping_tree_size tree` as its internally computed fuel.
`phase1_surface_unary_expression_recursive_grouping_sufficient_fuel_from_derivation`
proves that this bound is sufficient on every derived unary tree. Each negated
operand is a strict subtree, so its size fits the decremented bound. A postfix
leaf uses the already proved postfix normalizer and its own computed grouping
bound. The overall tree-size bound is sufficient, not claimed minimal.

The arithmetic suffix traversals recurse over finite lists and call their
lower-layer entry points directly. They do not depend on the older shared-fuel
normalizers' existential fuel witnesses or require a caller to select a common
fuel value for several operands.

## Sources and replay evidence

| Layer | Carrier and executable code | Derivation totality |
| --- | --- | --- |
| Unary | [GrammarAstUnaryExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstUnaryExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstUnaryExpressionRecursiveGroupingSpineTotality.v) |
| Multiplicative | [GrammarAstMultiplicativeExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstMultiplicativeExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstMultiplicativeExpressionRecursiveGroupingSpineTotality.v) |
| Additive | [GrammarAstAdditiveExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstAdditiveExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstAdditiveExpressionRecursiveGroupingSpineTotality.v) |
| Shift | [GrammarAstShiftExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstShiftExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstShiftExpressionRecursiveGroupingSpineTotality.v) |

[GrammarAstArithmeticRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstArithmeticRecursiveGroupingExamples.v)
proves a canonical grammar derivation for a mixed-precedence fixture. Its
evaluated controls inspect the typed values at every leading and suffix operand,
check all seven binary operator choices in order, and reconstruct the whole
tree exactly. Other controls cover twelve unary negations around nested grouping,
zero fuel, a legacy retained-constructor primary beneath negation, an existing
fully refined shift-carrier adapter, and exact preservation of a named postfix
leaf. Wrong unary markers, mismatched operator indices/literals, and malformed
grouping inside a later shift operand are rejected.

The legacy shift fixture uses node-count fuel as a concrete regression control.
It does not establish a universal fuel bound for the old shared-fuel decoder;
the new universal bound is for the new unary entry point.

These fixtures exercise grammar structure, including tuple operands. They do
not assert that the example expressions are well typed or have an arithmetic
evaluation.

The [source-spine workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
retains its existing targets and adds all nine new modules under Rocq 9.2.0.
It checks twenty-four configured theorem assumptions, including the new unary
size bound and the public reconstruction/totality results at all four layers,
requires closure under the global context, and runs the full recursive
compiled-proof checker. The evidence artifact records the new source and object
identities alongside the earlier grouping and representation evidence.

Nineteen existing prerequisite modules receive bounded import and proof-script
repairs. Six decoder-local pattern binders are renamed from `right` to
`right_operand` because Rocq 9.2 otherwise resolves that pattern name as the
`sumbool.right` constructor. These are alpha-renamings of local variables;
decoder branches, calls, fields, operator enums, and theorem statements remain
the same. The dependency cleanup uses the old refined definitions and shallow
totalities actually consumed by this slice. It does not add the old full
shared-fuel totality/support chain to the new proof's premises.

## Remaining composition boundary

This completes propagation of the recursive grouping refinement through unary,
multiplicative, additive, and shift operator fields. The existing enclosing
base-choice/expression, term-argument, effect-requirement, and record/data
carriers still need to consume the replacement shift carrier and lift their
correspondence proofs accordingly.

The immediate field is `Phase1BaseExpressionShiftRefinedShift`, which still
contains the old shift carrier. A focused successor should then use the new
base carrier in both the ordinary expression's main base and its `reject`
fallback operand. Those are separate arithmetic-bearing positions; updating
the main base alone would leave the fallback operand on its older carrier.

The prior shift-refined record/data route reaches these expressions through
the `effects ... within ...` generic-requirement alternative. That restricted
route cannot establish coverage of every generic requirement, declaration body,
or complete source AST.

The lower grouping carrier retains its documented command/fallback boundaries.
Named-postfix static and term-argument payloads keep their existing representation.
Other ordinary-expression forms inside grouping children still use generic
structural constructors; this operator-field lift does not make them a complete
semantic AST. The formal claim remains about token-level grammar trees, with
source-byte lexing, faithful production AST correspondence, and the broader
implementation-interface coverage contract retaining their separate obligations.
