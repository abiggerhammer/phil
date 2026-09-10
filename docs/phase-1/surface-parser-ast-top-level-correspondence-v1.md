# Phase 1 surface parser AST top-level correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #874.

#874 established the first converse-side correspondence at the outer `source_file` spine: optional module declarations, repeated imports, qualified names, optional import selections, and top-level declaration segmentation/count now decode from the certified reference tree and mechanically agree with the span-insensitive production `GrammarV1SourceFile` projection.

This slice descends one grammar level:

```text
top_level_decl = { attribute }, declaration ;
attribute = "@", identifier, "(", metadata_string_literal, ")" ;
```

and closes the structural choice surface for:

```text
declaration =
    record_decl
  | data_decl
  | type_alias_decl
  | claim_decl
  | callable_contract_decl
  | function_decl
  | provider_contract_decl
  | provider_implementation_decl
  | opaque_provider_implementation_decl
  | protocol_decl
  | capability_decl
  | boundary_decl
  | architecture_decl
  | component_decl
  | program_decl
  ;
```

## Certified top-level projection

`Phil.Surface.GrammarV1.ReferenceAstTopLevel` consumes only the certified tree exposed by #872. It validates:

- the exact `top_level_decl` two-item sequence;
- the repeated `attribute` node structure;
- attribute `@`, identifier, parentheses, and `metadata_string_literal` leaves;
- the exact `declaration` alternative node; and
- the exact nonterminal selected by each of the fifteen alternative indices.

The production projection erases source spans and declaration bodies, retaining exactly:

- ordered attribute name/value pairs; and
- the declaration-family constructor tag.

The certified projection must equal that production projection for every accepted fixture in the full Phase 1 surface corpus.

## Exhaustive declaration-choice control

The correspondence function explicitly maps all fifteen Grammar-v1 declaration alternative indices. The dedicated gate synthesizes one certified-tree-shaped declaration node for every alternative and requires the result sequence to equal the complete bounded Haskell declaration-tag enumeration.

It also proves fail-closed behavior for:

- an index/name mismatch; and
- an out-of-range alternative index.

This makes the declaration-choice mapping exhaustive independently of which declaration families happen to occur in the finite corpus.

A direct source fixture with multiple Unicode-valued attributes additionally checks the real lexer → certified tree → attribute projection → production parser path.

## Evidence boundary

This slice establishes exact top-level attribute and declaration-family choice correspondence, but declaration bodies remain opaque. It does not yet translate the bodies of record/data/type/claim/callable/function/provider/protocol/capability/boundary/architecture/component/program declarations or their nested syntax families.

Therefore:

- `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**;
- `PHIL-ASSURE-IMPL-CORR-001` remains unpromoted; and
- successor slices descend declaration-family-by-declaration-family until the certified-tree → production AST translation is total across Grammar v1.
