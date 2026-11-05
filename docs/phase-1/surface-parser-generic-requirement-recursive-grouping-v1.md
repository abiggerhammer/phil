# Generic-requirement recursive grouping correspondence v1

This bounded PHIL-SURFACE-GRAMMAR-CORR-001 G3 continuation composes the
effect-set recursive grouping carrier into alternative 6 of the thirteen-way
`generic_requirement` grammar choice:
`effects <identifier> within <effect_set_expression>;`.

`Phase1SurfaceGenericRequirementRecursiveGroupingSpine` directly retains
the identifier parse tree and `Phase1SurfaceEffectSetRecursiveGroupingSpine`
for Effects. All twelve other alternatives copy exact typed/proposition
children from `Phase1SurfaceGenericRequirementPropositionSpine`, with
unchanged choice indices 0–5 and 7–12. The shell and raw entry points use the
existing proposition route. The legacy converter exhaustively matches all
thirteen constructors of
`Phase1SurfaceGenericRequirementExpressionFallbackBaseChoiceShiftRefinedSpine`
and invokes only the effect-set legacy converter on the Effects child;
it never reparses full legacy erasures.

Round-trip evidence preserves each of the five Effects sequence items, the
identifier, syntax, choice index, optional-argument interiors, ordered and
repeated effect members, and whole source parse tree. Shell, raw-tree and
legacy public totality require only canonical `Derives`: no child-success or
caller-supplied fuel hypotheses.

## Evidence and validation

- `GrammarAstGenericRequirementRecursiveGroupingSpine.v`: full carrier,
  shell/raw and direct legacy conversion, complete source reconstruction.
- `GrammarAstGenericRequirementRecursiveGroupingSpineTotality.v`:
  canonical-Derives totality; extracts the actual fifth-item effect-set
  derivation rather than reparsing a complete legacy requirement.
- `GrammarAstGenericRequirementRecursiveGroupingExamples.v`:
  empty, ordered multi-member, reference, direct legacy and negative controls.

All paths are relative to `proof/Phil/Surface/`. The source-spine workflow
preserves previous gates and adds three explicit compilation targets, three
assumption checks (53 total), two recursive checker endpoints (22 total), and
six source/object hashes (81 identities total; 78 artifact files under the
existing count convention). New modules compile under Rocq 9.2.0 with
`-w +all`.

Next: optional requirement lists through record/data declarations and the
retained implementation-representation field. Static-reference argument
interiors, named-postfix argument payloads, command/failure-target bodies,
generic grouping nested fallback boundaries, production AST binding, G2/G4,
and finite interface inventory remain separate. This bounded G3 carrier lift
does not promote the Logic Ledger or close Phase 1.
