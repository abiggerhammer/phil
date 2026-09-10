# Phase 1 surface parser AST fixed-command correspondence v1

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #895.

#889 established the ordinary expression spine while deliberately representing every `command_expression` payload as an opaque family tag. #895 closes session-expression structure. This slice begins replacing those command tags with exact certified-tree → production-AST payload correspondence.

The first command tranche covers the 15 fixed-shape families that do not introduce blocks, match arms, branch/failure helper payloads, or the omitted-vs-explicit-empty `continue`/`break` argument distinction:

- `receive_frame`, `receive_exact`, and typed `receive`;
- `recognize` and `validate`;
- `send_exact` and `send`;
- `commit_receive` and standalone `reject`;
- `close` and `release`;
- `convert`, `transport`, and `accept`; and
- `prove`.

For each family the decoder checks the exact certified nonterminal/sequence/literal shape and translates payloads through the correspondence layers already established for ordinary expressions (#889), static references (#883), recursive type payloads (#887), and propositions (#891). `base_expression` payloads are embedded into the already-checked expression-core decoder with no fallback, matching the grammar's distinction between `base_expression` and full `expression`.

Direct controls parse complete Grammar-v1 source through both the certified recognizer and production parser and compare the resulting fixed-command payload projections. Optional `using`/`at` payloads are exercised in both present and absent forms. An out-of-range certified alternative fails closed, and a block-bearing `construct` command is confirmed to remain outside this tranche on both sides.

## Evidence boundary

Nested ordinary-expression payloads still inherit #889's explicit command-family opacity: if a fixed command contains another command as an expression/base-expression child, the nested command's family is preserved but its body is not recursively expanded by this slice. Type payloads retain #887's named deeper expression/proposition holes, and static-reference arguments retain #883's shallow category boundary.

The remaining command families are `construct`, `borrow`, `if`, `match`, `decide`, `closure`, `loop`, `continue`, `break`, `select`, `offer`, and `fail`. The next command slice should close the small helper/argument families (`continue`, `break`, `select`, `fail`, and `construct`) before the block/match-arm tranche.

Accordingly `PHIL-SURFACE-GRAMMAR-CORR-001` remains **Active / Tested**, and `PHIL-ASSURE-IMPL-CORR-001` is not promoted.
