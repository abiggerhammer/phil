# Phase 1 architecture identity v1

This is the first implementation slice after the Phase 0 freeze and CI normalization. It is grounded in the current Phase 1 charter, ADR-019, and logic-ledger obligation `PHIL-ARCH-ID-001`.

The slice deliberately does **not** freeze new Phil source syntax. ADR-019 makes the checked semantic graph normative while deferring final architecture syntax, and the Phase 1 charter explicitly allows early generalized-language slices to expose awkward or incomplete surface forms before the normative grammar is frozen.

## What v1 establishes

The Core static-semantic substrate now distinguishes:

- `DeclarationKey`: stable declaration lineage, independent of human display name and module path;
- `InterfaceRevision`: the exact checked public semantic contract;
- `DefinitionRevision`: the exact checked definition under that interface;
- `InstanceKey`: one stable architecture occurrence;
- `InstanceRevision`: the exact declaration identity and static bindings for that occurrence; and
- `RealizationRevision`: the exact concrete realization choices for an architecture instance.

Exact revisions are derived from a versioned canonical semantic form rather than raw source text. Ordered semantic data remains ordered; explicitly unordered semantic sets and named record fields are canonicalized independently of insertion/container order.

Human-facing declaration presentation is carried separately from semantic revision inputs. Renaming a declaration or moving it between modules therefore does not change its semantic identity when its stable key and checked semantics are unchanged.

Child occurrence identity names the stable parent occurrence key rather than the complete parent definition revision. An unrelated sibling edit may therefore revise the containing architecture definition without recursively rekeying an unaffected child. Broader assurance evidence can still name the containing architecture revision in its validity context when that dependency is semantically real.

Concrete realization semantics are downstream of `ArchitectureInstance` identity. Replacing one implementation can therefore change `RealizationRevision` while preserving the exact abstract instance.

## Executable cases

The initial Core test corpus checks:

1. canonical record order independence;
2. canonical unordered-set order independence;
3. declaration rename/module-move invariance;
4. public-contract changes revising both interface and definition;
5. definition replacement under a stable interface;
6. distinct equal-looking architecture occurrences remaining distinct;
7. unrelated sibling edits not rekeying an unaffected child; and
8. realization replacement changing realization identity without changing the architecture instance.

These are executable implementation cases, not yet the Rocq proof required to close `PHIL-ARCH-ID-001`.

## Deliberate limits

This slice does not yet claim `PHIL-ARCH-IMPORT-001`, `PHIL-ARCH-INST-001`, or `PHIL-ARCH-REALIZE-001` as implemented. It does not yet provide the complete `ArchitectureDeclaration` graph, source elaboration, module/import resolution, provider qualification, generic Source/Core → Systems lowering, or witness migration.

The canonical representation is versioned and deterministic, but ADR-019 intentionally leaves the final compact serialization/digest choice open. A later identity/certification slice may content-address these canonical forms without changing their semantic equality rules.

The next architecture slice should make ordinary checked declarations elaborate into an explicit target-abstract architecture graph, then use that graph to remove the remaining witness-specific environment construction rather than adding program-name exceptions.
