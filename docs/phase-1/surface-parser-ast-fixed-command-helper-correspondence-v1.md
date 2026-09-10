# Phase 1 surface parser AST fixed-command helper correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #896 by replacing the remaining non-block command-family tags with exact certified-tree → production-AST payload correspondence.

## Closed in this slice

The correspondence layer now covers:

- `construct` target static references and ordered field assignments;
- `continue` argument payloads;
- `break` argument payloads;
- `select` branch qualified names, term arguments, optional `using` evidence, and endpoint;
- standalone `fail` targets, failure arguments, and endpoint.

`continue` and `continue()` (likewise `break`/`break()`) intentionally normalize to the same production AST list representation because the production AST does not retain whether empty parentheses were present. This is a documented source-syntax normalization rather than an omitted correspondence case.

Nested ordinary-expression payloads use the #889 expression-core correspondence. Static references use #883. Nested command expressions reached through #889 remain represented by the explicit command-family boundary until the block/match-arm tranche and final recursive integration close them.

## Remaining boundary

After this slice, the only command-expression families still structurally opaque are the seven block/match-arm families:

- `borrow`
- `if`
- `match`
- `decide`
- `closure`
- `loop`
- `offer`

Deeper mutually recursive static/type argument payload integration and the remaining declaration bodies also remain open.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted.
