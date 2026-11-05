# Recursive grouping correspondence v1

This is a bounded proof slice for `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`dd1a40b5948a72e420a786c4c5de5d1c2e1ac24d`. It does not change the Logic Ledger
status or the Phase 1 exit contract. The companion
[implementation-correspondence inventory](implementation-correspondence-inventory-v1.md)
records the wider production-binding boundary.

## What the slice adds

The earlier parenthesized-expression and tuple-expression spines retained their
child expressions as raw `ParseTree` values. The new mutually recursive
`Phase1SurfaceRecursiveGroupingTree` and
`Phase1SurfaceRecursiveGroupingExpression` carriers give these nodes recursively
normalized expression children. Every tuple element is included, including all
elements in its repeated suffix.

The transformation follows the surrounding grammar structure, so it reaches
grouping nodes inside nested arithmetic, named arguments, and other ordinary
parse-tree positions. It preserves nonterminal names, alternative indices,
literal and lexical leaves, list order, optionality, and repetition. The adapter
`phase1_surface_refine_expression_outer_grouping_fuel` connects this refinement
to the existing expression outer-spine carrier.

Command-expression bodies and fallback bodies remain explicit raw-tree
boundaries. Traversal stops at those bodies. Other expression forms retain
their generic structural constructors; this slice does not supply a dedicated
semantic AST constructor for every expression form.

## Checked claims

| Claim | Theorem and scope |
| --- | --- |
| Exact reconstruction | `phase1_surface_normalize_recursive_grouping_fuel_round_trip`: whenever normalization returns a value, reconstructing it returns the exact input tree. This implication holds for arbitrary input trees and fuel. |
| Grammar supplies the preconditions | `phase1_surface_grouping_well_formed_from_derivation_mutual`: every tree in a canonical Grammar-v1 derivation has the required structural well-formedness. Its proof uses mutual induction over ordinary, sequence, and repetition derivations and the existing shallow decoder totality lemmas. |
| Effective fuel bound | `phase1_surface_recursive_grouping_sufficient_fuel`: the computable number of nodes in the input parse tree is sufficient fuel for every well-formed tree. The argument uses strict subtree size; it does not assume successful recursive normalization. |
| Totality on derived trees | `phase1_surface_recursive_grouping_total_from_derivation`: every Grammar-v1-derived tree normalizes at that computed bound, and the result reconstructs the original tree. The only domain premise is the grammar derivation. |
| Typed expression result | `phase1_surface_recursive_grouping_expression_total_from_derivation`: a derived `expression` yields the recursive expression carrier at the same computed bound, with exact reconstruction. |

The well-formedness predicate is an internal proof device. Its shallow-decoder
premises are discharged from the grammar before the public totality claim; they
are not a caller-supplied recursive-success oracle. The bound counts all input
nodes, including retained boundaries, and is sufficient rather than minimal.
The public `phase1_surface_normalize_recursive_grouping` and
`phase1_surface_normalize_recursive_grouping_expression` entry points compute
that bound internally, so callers do not choose fuel.

These claims concern outputs obtained by the normalizer. The carrier also has
generic structural constructors, so an arbitrary hand-built carrier value is
not certified as a valid grammar derivation. The normalizer is not a substitute
for the reference grammar recognizer.

## Evidence and replay

The proof is split into four modules:

- [GrammarAstRecursiveGrouping.v](../../proof/Phil/Surface/GrammarAstRecursiveGrouping.v): carriers, executable fuelled transformation, reconstruction, and outer-spine adapter.
- [GrammarAstRecursiveGroupingWellFormed.v](../../proof/Phil/Surface/GrammarAstRecursiveGroupingWellFormed.v): grammar-derived structural preconditions.
- [GrammarAstRecursiveGroupingTotality.v](../../proof/Phil/Surface/GrammarAstRecursiveGroupingTotality.v): subtree argument, computable size bound, and totality.
- [GrammarAstRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstRecursiveGroupingExamples.v): a canonical grammar derivation for the nested positive fixture, plus evaluated recursive, malformed-input, fuel, and retained-boundary controls.

The existing
[source-spine correspondence workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
compiles these modules with Rocq 9.2.0, checks the five claims above with
`Print Assumptions`, requires them to be closed under the global context, and
runs the independent compiled-proof checker. The artifact includes the new
sources and compiled modules, their hashes, and the assumption-check output.
The workflow also replays its existing source and top-level representation
targets.

The prerequisite import cleanup makes the existing parenthesized and tuple
spines depend on their actual structural helpers. It preserves their decoder
definitions and theorem statements and avoids pulling unrelated type-payload
proofs into this slice. Small repairs to the existing parenthesized and tuple
proof scripts make their induction and reconstruction steps replay under the
same Rocq version.

## Remaining proof boundary

This adds a total, lossless recursive grouping refinement on grammar-derived
trees. It does not establish correspondence to the Haskell `GrammarV1SourceFile`
output, alter the production parser, or expand the existing record/data
implementation carrier automatically. A successor must compose the refinement
into the selected larger carrier and its representation proof.

Recursive command/fallback payloads, dedicated carriers for the other recursive
expression/type/proposition/session/effect forms, complete declaration-body
translation, and the faithful production AST binding retain their own proof
obligations. Lexical tokens remain the canonical grammar's token-level input;
this is not a proof of source-byte tokenization or Unicode normalization.
Both active umbrella targets retain their existing status.
