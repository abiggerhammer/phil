# Effect-set recursive grouping correspondence v1

This is a bounded continuation of `PHIL-SURFACE-GRAMMAR-CORR-001`, based on
`838cd27598edf23aa43d5e1a7b3251e45b489a8e`, the merge of the
[effect-expression composition](surface-parser-effect-expression-recursive-grouping-v1.md).
It replaces every member of an effect-set literal with that slice's effect
carrier and carries the literal through the enclosing literal/reference choice.
It records further formal evidence toward G3 in the
[implementation inventory](implementation-correspondence-inventory-v1.md).
It does not change a Logic Ledger status or the Phase 1 exit contract.

## Fields replaced and structure preserved

| Carrier | Representation and contract |
| --- | --- |
| `Phase1SurfaceEffectSetLiteralRecursiveGroupingSpine` | A list of `Phase1SurfaceEffectExpressionRecursiveGroupingSpine` values, preserving every member, order, and multiplicity |
| `Phase1SurfaceEffectSetRecursiveGroupingSpine` | A literal containing that new list carrier, or the existing complete static-reference carrier |

The new records store their replacement children directly, without a duplicate
old carrier or input tree. The literal's empty list denotes the present syntax
`{}`. It is distinct from a nonempty literal whose members have absent term
arguments or present empty `()` arguments. The existing effect carrier preserves
those member-level cases independently.

The enclosing grammar choice remains alternative 0 for an effect-set literal
and alternative 1 for a static reference. The reference branch copies the
existing `Phase1SurfaceStaticReferenceSpine` directly in shell and legacy
conversion, including its qualified name and retained optional static arguments.
Static-argument interiors remain at their preceding representation and validation
scope. The effect-set carrier preserves the source sequence, including repeated
effect names; these are grammar-tree results, not effect-set semantic equations.

## Executable entry points and proof contracts

| Layer | Raw-tree entry point | Direct legacy adapter |
| --- | --- | --- |
| Literal | `phase1_surface_normalize_effect_set_literal_recursive_grouping_tree` | `phase1_surface_refine_effect_set_literal_recursive_grouping` |
| Literal/reference choice | `phase1_surface_normalize_effect_set_recursive_grouping_tree` | `phase1_surface_refine_effect_set_recursive_grouping` |

The corresponding `_spine` normalizers consume the old shallow
`Phase1SurfaceEffectSetLiteralSpine` and `Phase1SurfaceEffectSetSpine` values.
Raw normalizers compose those conversions with the existing shell decoders.
The legacy adapters accept the full shift-refined literal and choice carriers.

The raw list conversion invokes the new effect raw normalizer on every member.
The legacy list conversion invokes the direct effect legacy adapter on every
old effect carrier. Both have exact map-of-erasure theorems. For the raw list,
successful conversion establishes:

```coq
map phase1_surface_effect_expression_recursive_grouping_spine_tree refined = effects
```

The legacy theorem equates that new erasure list with the complete list of old
effect erasures. These equalities preserve count, order, multiplicity, and every
member's complete tree. Literal shell reconstruction additionally gives equality
of the old shallow carrier; tree reconstruction preserves braces, comma pairs,
and the optional empty/nonempty entries shape.

Choice reconstruction preserves the exact old constructor and its payload.
The unconditional legacy reference-preservation theorem returns the identical
reference carrier in the new reference constructor. It does not require that
carrier to have been produced by an earlier normalizer.

The totality proof obtains a `Forall` certificate of actual effect-expression
derivations from the literal derivation. It handles the empty optional entries,
the first effect, and every repeated comma/effect suffix. The raw and legacy
list traversals independently consume those certificates through the preceding
effect-expression totalities. The enclosing literal branch supplies its own
literal derivation, and the reference branch preserves its carrier.

All six public literal/choice shell, raw-tree, and legacy totality theorems
require only the corresponding canonical `Derives` judgment. There is no
caller-supplied fuel, successful-child-normalization premise, or separate
canonical-constructor hypothesis.

Grammar validity is supplied by the derivation certificate. Reconstruction alone
does not certify arbitrary hand-built values, typing, effect semantics,
source-byte lexing, or production AST behavior.

## Sources and replay evidence

| Module | Evidence |
| --- | --- |
| [GrammarAstEffectSetRecursiveGroupingSpine.v](../../proof/Phil/Surface/GrammarAstEffectSetRecursiveGroupingSpine.v) | Literal/list and choice carriers, raw and direct legacy conversions, exact reconstruction, and reference preservation |
| [GrammarAstEffectSetRecursiveGroupingSpineTotality.v](../../proof/Phil/Surface/GrammarAstEffectSetRecursiveGroupingSpineTotality.v) | Derivation-only totality for every literal member and all six public entry points |
| [GrammarAstEffectSetRecursiveGroupingExamples.v](../../proof/Phil/Surface/GrammarAstEffectSetRecursiveGroupingExamples.v) | Nineteen checked integration and rejection controls |

The examples derive empty and three-member literals and both enclosing grammar
alternatives. They exercise empty, singleton, and longer literal lists. The
three ordered members share a dotted reference with retained `[Unit]` static
arguments and differ in their term arguments: absent, present empty, and a
present complete three-expression list. Typed-field controls inspect those
exact positions, including the later reject operand inside the final member.
Separate controls check complete-list erasure, whole-tree reconstruction, both
legacy literal/choice adapters, and exact reference-branch preservation.

The prior effect derivations are reused through ordinary-derivation path
transport and a local token-suffix extension lemma. The latter leaves later
commas and the closing brace unconsumed; right cancellation of list append
preserves repetition progress. These helpers make no invariance claim about
oracle-resolved or lookahead-sensitive parsing.

Negative controls reject a malformed later reject operand, a wrong separator,
a trailing comma, a wrong closing delimiter, an unknown choice index, and a
mismatched branch marker. Node-count fuel in the old-decoder fixture is only a
concrete compatibility control, not a universal bound for that decoder. The
new entry points have no fuel parameter.

The [source-spine workflow](../../.github/workflows/phase1-surface-grammar-rocq-source-spine-correspondence.yml)
retains its prior targets and adds all three new modules under Rocq 9.2.0.
It checks fifty configured theorem assumptions for closure under the global
context and runs the full recursive compiled-proof checker over twenty
configured totality/example endpoints and their dependencies. The accumulated
artifact contains seventy-two files and seventy-five recorded identities,
including all three new source/object pairs.

Seven existing effect-set prerequisite modules receive direct-owner import and
proof-script repairs. Their definitions and theorem statements remain unchanged.
The new route uses the shallow effect-set totalities and the new effect-expression
totalities, without the old full shared-fuel totality/support chain.

## Remaining composition boundaries

The next selected consumer is the effect-set payload in the
`effects <identifier> within <effect_set_expression>;` generic-requirement
alternative, index 6. Its lift must preserve the identifier and branch syntax
while carrying this effect-set value. The established route then proceeds
through optional requirement lists in record/data declarations and the
corresponding retained implementation-representation field. Coverage of the
other generic-requirement branches and declaration bodies remains explicit.

Static-reference argument interiors, named-postfix argument payloads, command
bodies, failure-target arguments, and the generic grouping expression's nested
fallback boundary retain their existing representations. Faithful production
AST binding, source-byte lexing, and the finite implementation-interface coverage
contract remain separate obligations. This slice does not close G2 or G4 or
promote an umbrella target.
