# Generic-requirements list and optional recursive grouping correspondence v1

PHIL-SURFACE-GRAMMAR-CORR-001 G3 continuation after #1586.

The preceding slice certified one thirteen-way `generic_requirement`, with the
Effects branch carrying its recursively grouped effect-set representation.
This bounded lift composes that **same exact value** through the ordered
`generic_requirements` repetition and `EOptional` wrapper.

`Phase1SurfaceGenericRequirementsRecursiveGroupingSpine` retains a list of
`Phase1SurfaceGenericRequirementRecursiveGroupingSpine` values. Its
normalizers preserve whole-tree erasure for every successful list and optional
normalization. Canonical `Derives` suffices for totality, including the absent
optional and present-but-empty `requires {}` cases; there are no caller-supplied
fuel or child-success hypotheses.

The only new proof artifacts are
`GrammarAstGenericRequirementsRecursiveGroupingSpine.v`,
`GrammarAstGenericRequirementsRecursiveGroupingSpineTotality.v`, and
`GrammarAstGenericRequirementsRecursiveGroupingExamples.v`.
The source-spine CI target/assumption/recursive-checker/identity inventory is
extended accordingly (47 explicit targets, 56 assumptions, 24 recursive
checker endpoints, 87 identities). The prepublication hosted Rocq 9.2.0
scratch workflow provides a complete replay before PR publication.

**Boundary:** This does not yet replace the optional field inside record/data
declarations or implementation-representation consumers. No Grammar-v1,
production AST, evaluation, G2/G4, or Logic Ledger semantics change. Static
reference interiors, named-postfix arguments, command and failure-target
bodies, nested fallback boundaries, and finite interface inventory remain
separate proof work.
