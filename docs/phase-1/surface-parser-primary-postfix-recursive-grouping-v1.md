# Primary and postfix recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`9cf11bc88ff4b3d006e1f34336151b4ae7a30506`, the merge of the
[recursive grouping slice](surface-parser-recursive-grouping-correspondence-v1.md).
It records a formal carrier refinement. It does not change the Logic Ledger
status or the Phase 1 exit contract.

## The composition gap

The recursive grouping transformation already traversed ordinary parse-tree
positions and replaced parentheses and tuple children with recursive expression
values. The established primary-expression carrier still held the older,
shallow parenthesized and tuple spines. Its immediate postfix consumer therefore
continued to carry raw expression children at those positions.

This slice provides a replacement primary carrier and a postfix carrier that
uses it directly. Neither stores a copy of the old primary carrier beside a
second normalized tree.

## Representation and executable adapters

`Phase1SurfacePrimaryExpressionRecursiveGroupingSpine` has the nine alternatives
of the canonical `primary_expression` grammar:

| Grammar alternative | Carrier payload |
| --- | --- |
| Tuple | First and second `Phase1SurfaceRecursiveGroupingExpression` values, followed by a list of further values of that same type |
| Parenthesized expression | One `Phase1SurfaceRecursiveGroupingExpression` |
| `true`, `false`, `unit` | Three separate constructors |
| Character, runtime string, float, integer | Four separate constructors carrying the exact lexical spelling |

The tuple representation enforces its minimum arity structurally. All repeated
tuple elements receive the same recursive treatment as the first two. Literal
spellings remain token payloads; this proof does not interpret numbers, check
source-byte lexing, or equate different spellings.

`phase1_surface_normalize_primary_expression_recursive_grouping_tree` first
uses the computed-fuel grouping transformation, then projects the exact nine
primary alternatives. The projection checks the primary branch, the selected
node, and the lexical class. Reconstruction preserves the exact tree, including
parentheses, tuple delimiters, branch indices, and lexical payloads.

The adapter `phase1_surface_refine_primary_expression_recursive_grouping`
reconstructs an existing integer-refined primary carrier and normalizes that
tree. This choice matters for its domain: an arbitrary old carrier can have a
valid grammar-derived erasure even when it was not itself produced by the old
normalizer. For example, its retained lexical constructor can hold a valid
parenthesized expression. The new adapter handles such values according to
their erasure instead of imposing an unstated canonical-constructor premise.

The replacement postfix carrier embeds the new primary carrier together with
the existing ordered projection-name list. Its named branch preserves the
existing refined named-postfix carrier, including its static/term-argument and
projection structure. Adapters connect both the existing postfix carrier and
raw `postfix_expression` trees to this replacement.

## Proof obligations discharged by this slice

The public theorem package establishes the following for both primary and
postfix expressions:

1. **Exact reconstruction on success.** If the executable normalizer returns a
   carrier, reconstructing that carrier returns the identical input parse tree.
   This implication applies even to inputs without a supplied derivation.
2. **Totality from the grammar.** Every canonical Grammar-v1 derivation of the
   relevant nonterminal yields a successful normalization result and exact
   reconstruction. The caller supplies the grammar derivation; no separate
   recursive-normalization-success or fuel premise is required.
3. **Compatibility with the old carrier.** If an existing carrier's erasure has
   the relevant grammar derivation, its executable adapter succeeds and the
   new carrier has the same erasure.

The raw normalization functions compute their grouping fuel internally using
the previously proved tree-size bound. The primary proof covers all nine
grammar alternatives. The postfix proof combines the primary result with the
existing named-branch and projection-spine correspondence.

As with the preceding slice, these statements certify normalized outputs and
grammar-derived inputs. They do not assert that every hand-built recursive
carrier inhabitant is a grammar derivation, nor that normalization alone is a
complete grammar recognizer.

## Evidence and replay

The implementation and proof are in:

- [GrammarAstPrimaryExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstPrimaryExpressionRecursiveGroupingSpine.v) and its [totality companion](../../proof/Phil/Surface/GrammarAstPrimaryExpressionRecursiveGroupingSpineTotality.v).
- [GrammarAstPostfixExpressionRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstPostfixExpressionRecursiveGroupingSpine.v) and its [totality companion](../../proof/Phil/Surface/GrammarAstPostfixExpressionRecursiveGroupingSpineTotality.v).
- [GrammarAstPrimaryPostfixRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstPrimaryPostfixRecursiveGroupingExamples.v).

The examples inspect recursively typed tuple and parenthesized children,
exercise all seven keyword/lexical alternatives, and prove canonical grammar
derivations for the nested tuple and its postfix projection wrapper. They also
check exact reconstruction, projection ordering, compatibility with old
retained-constructor values, and rejection of malformed grouping, an unknown
primary branch, and a wrong lexical class. Named-postfix controls preserve the
existing branch boundary.

The [source-spine correspondence workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
compiles the new modules under Rocq 9.2.0 alongside the original recursive
grouping proof and the existing representation targets. It checks the public
round-trip and totality theorems with `Print Assumptions`, requires closure under
the global context, and runs the independent compiled-proof checker. Source and
compiled-module identities and the assumption output accompany the workflow
artifact.

The prerequisite cleanup makes existing definition modules import the helpers
they actually use instead of depending on unrelated predecessor totality files.
The named-postfix representation genuinely depends on existing static/type
carriers; those dependencies are retained. Existing endpoint totality modules
are replayed as regression checks. Any accompanying proof-script repairs retain
their theorem statements and executable definitions.

## Exact remaining boundary

This completes the immediate primary-to-postfix consumer step. It does not
automatically change the existing unary, multiplicative, additive, shift,
generic-requirement, or record/data carriers. The next composition must replace
their consumed postfix field and lift the corresponding reconstruction and
derivation-totality proofs through that chain.

The [arithmetic continuation](surface-parser-arithmetic-recursive-grouping-v1.md)
performs the unary, multiplicative, additive, and shift consumer lifts, including
every repeated suffix operand. Its own record states the remaining enclosing
expression/source composition boundary.

The existing shift-refined record/data chain reaches this expression path
through the `effects ... within ...` generic-requirement alternative. Its other
generic-requirement alternatives, retained type/field payloads, and other
declaration families require their stated refinements. A source-wide theorem
cannot be inferred from this local consumer lift.

Command-expression and fallback bodies remain the explicit raw boundaries of
the recursive grouping carrier. The named branch keeps its existing static and
term-argument payload representation; this slice does not recursively replace
those argument fields. Other ordinary expression forms inside grouping children
continue to use the generic structural constructors from the preceding slice.

There is no change here to the Haskell parser or its returned `GrammarV1SourceFile`.
The faithful production AST binding and complete production behavior remain
separate obligations in the
[implementation-correspondence inventory](implementation-correspondence-inventory-v1.md).
Both active umbrella targets retain their existing status.
