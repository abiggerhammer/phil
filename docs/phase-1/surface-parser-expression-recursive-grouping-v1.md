# Expression recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`9662568df0debc8ddcf6a0f8d3c7c14e2594c83c`, the merge of the
[unary/arithmetic composition](surface-parser-arithmetic-recursive-grouping-v1.md).
It lifts that slice's shift carrier through the enclosing base expression,
fallback, and ordinary-expression shell. It records further formal evidence
toward G3 in the [implementation inventory](implementation-correspondence-inventory-v1.md).
It does not change a Logic Ledger status or the Phase 1 exit contract.

## Fields replaced

| Layer | Replacement | Structure preserved |
| --- | --- | --- |
| Base expression | The shift branch contains `Phase1SurfaceShiftExpressionRecursiveGroupingSpine` | The command/shift alternative and the exact command tree |
| Fallback | The reject branch contains the new base-expression carrier | The fail/reject alternative, keyword, and exact failure-target tree |
| Expression | The main base and the optional fallback both contain their new carriers | Sequence order, optional presence, `or`, and both independent operand positions |

The main expression base and the reject-fallback base are distinct fields. The
new expression normalizer converts both. The former shift-refined expression
carrier advanced only its main base; its fallback still used the older
base-choice representation.

The new records store the replacement child carriers directly. They do not
retain an old carrier or duplicate original tree alongside those children.
Reconstruction functions compute the old shallow views from the new values.

## Executable entry points and proof contracts

The raw-tree entry points are:

- `phase1_surface_normalize_base_expression_recursive_grouping_tree`
- `phase1_surface_normalize_fallback_recursive_grouping_tree`
- `phase1_surface_normalize_expression_recursive_grouping_tree`

Each composes an existing shallow decoder with a child-carrier conversion. This
reuses the existing alternative-index, keyword, sequence-length, and optional
shape checks. The new arithmetic-bearing fields invoke the already proved
grouping-aware entry points.

At every layer the public theorems establish exact input-tree reconstruction
whenever normalization succeeds. The shell theorems additionally establish
equality of the reconstructed old shallow carrier, including its selected
branches and both fields. The optional-fallback theorem reconstructs the old
option by mapping the fallback reconstruction over the converted option; it
preserves both absence and presence.

Totality follows from a canonical Grammar-v1 derivation of `base_expression`,
`fallback`, or `expression`, respectively. The expression proof extracts the
main base derivation and the independent optional-tail derivation. In the
present-tail case it obtains the fallback derivation from the `or` sequence;
the reject branch then obtains its own base derivation. Each required child
conversion is discharged by the corresponding lower-layer theorem.

The public entry points require no supplied fuel, shared fuel witness, or
successful-child-normalization premise. This layer adds finite choice/option
composition over the arithmetic entry points and their already proved bounds.

The compatibility adapters are:

| Adapter | Existing input carrier |
| --- | --- |
| `phase1_surface_refine_base_expression_recursive_grouping` | `Phase1SurfaceBaseExpressionShiftRefinedSpine` |
| `phase1_surface_refine_fallback_recursive_grouping` | `Phase1SurfaceFallbackBaseChoiceSpine` |
| `phase1_surface_refine_expression_recursive_grouping` | `Phase1SurfaceExpressionFallbackBaseChoiceShiftRefinedSpine` |

Their totality requires only the relevant grammar derivation of the old value's
erasure. An old value need not have been produced by a particular normalizer.
The base and expression adapters use the new raw normalizers on those erasures;
the fallback adapter directly converts its old shallow carrier.

Grammar validity is supplied by the derivation certificate. Exact reconstruction
does not certify arbitrary hand-built carrier values or the interiors of
retained tree boundaries.

## Sources and replay evidence

| Layer | Carrier and executable code | Derivation totality |
| --- | --- | --- |
| Base expression | [GrammarAstBaseExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstBaseExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstBaseExpressionRecursiveGroupingSpineTotality.v) |
| Fallback | [GrammarAstFallbackRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstFallbackRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstFallbackRecursiveGroupingSpineTotality.v) |
| Expression | [GrammarAstExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstExpressionRecursiveGroupingSpine.v) | [SpineTotality.v](../../proof/Phil/Surface/GrammarAstExpressionRecursiveGroupingSpineTotality.v) |

[GrammarAstExpressionRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstExpressionRecursiveGroupingExamples.v)
contains fourteen checked controls. A grammar-derived expression combines the
preceding multi-operator arithmetic fixture in its main base with a different
reject operand containing seven negations and seven groups. The controls inspect
the actual typed operands on both sides and reconstruct the complete tree.
They also exercise the old expression/fallback adapters, absent fallback,
reject-command preservation, and exact command/failure-target preservation.

A second grammar-derived fixture retains a command and a fail target containing
grouped term arguments. It checks exact retention of that nontrivial payload,
without claiming a refinement of the failure-target interior. Negative controls
reject a wrong `or` marker, a mismatched fallback keyword, and malformed later
arithmetic operands independently in the main and reject positions. A legacy
fallback with invalid erasure is also rejected.

The legacy expression fixture supplies node-count fuel to the older decoder as
a concrete compatibility control. This is not a universal sufficient-fuel
theorem for that decoder. The new expression entry point has no fuel parameter.
As in the preceding slice, tuple operands in the arithmetic fixture establish
grammar structure without asserting typing or arithmetic evaluation.

At this slice's merge, the [source-spine workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
retained its prior targets and added all seven new modules under Rocq 9.2.0. It
inspected thirty-three configured theorem assumptions, required closure under
the global context, and ran the full recursive compiled-proof checker over the
new totalities and examples with their dependencies. The artifact included the
new source/object pairs, producing fifty-four files and fifty-seven recorded
source/object identities across the accumulated evidence.

Twelve existing prerequisite modules received direct-owner import and proof-script
repairs. Their definitions and theorem statements remain unchanged. The new
proofs consume the shallow choice/optional totalities and the old adapter input
definitions; they do not import the old full shared-fuel totality/support chain.

## Remaining composition boundaries

This completes the outer base/fallback/expression-shell lift. At this slice's
merge, the term-argument carriers still contained the old expression
representation. The subsequent
[term-argument continuation](surface-parser-term-arguments-recursive-grouping-v1.md)
replaces every expression in that outer list and proves exact preservation of
the complete list, its order, commas, and parentheses.

The next consumer after that continuation is optional effect arguments,
followed by effect-set literals, the `effects ... within ...` generic-requirement
branch, and the established record/data route. The effect-argument lift must
distinguish absent arguments from present empty `()` arguments. This restricted
route is not evidence for every generic requirement, declaration body, or
complete source AST.

The generic recursive-grouping expression type used inside parenthesized/tuple
children still has its own retained fallback `ParseTree` boundary. Replacing
the outer expression shell does not change that nested recursive type. Other
ordinary-expression forms in those grouping children retain generic structural
constructors. These are separate recursive-composition obligations.

Command-expression and failure-target interiors remain exact trees. Named
postfix static and term arguments also retain their preceding representation.
Source-byte lexing, faithful production AST correspondence, and the finite
implementation-interface coverage contract remain separate obligations.
