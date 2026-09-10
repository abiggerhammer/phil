# Grammar-v1 recursive command-closure correspondence

This slice continues `PHIL-SURFACE-GRAMMAR-CORR-001` after #900.

#896, #897, and #900 establish exact certified-tree/production-AST payload correspondence for all 27 `command_expression` alternatives at their own wrapper level. #889 deliberately represented any command encountered while recursively decoding an ordinary expression as only its command-family name.

This slice closes that remaining command-family opacity without introducing a second recursive AST or Haskell module cycles.

For a complete `expression` pair, the checker first requires #889's ordinary expression-core projection to agree. It then:

- walks the production expression transitively through command payloads, blocks/statements, types, static references and all static-argument forms, static values, effects, propositions, and sessions;
- collects every reachable production command expression and orders them by source span;
- collects every certified `command_expression` node by lexical DFS from the reference parse tree; and
- checks each paired occurrence with the exact #896 fixed-command, #897 helper-command, or #900 block-command decoder.

Direct controls place commands beneath nested command payloads, block bodies, static type arguments, effect-set arguments, session parameter types, Proof/claim arguments, term arguments, fallbacks, and construct/match bodies. A mismatched command-family control must fail closed.

This closes recursive *command* correspondence for the tested expression graph. Static-reference arguments are still represented by the earlier shallow argument tags when their non-command payload values are compared, so deep mutually recursive type/session/static-value/effect-set argument equality remains a separate successor. Remaining declaration bodies also remain to be translated.

`PHIL-SURFACE-GRAMMAR-CORR-001` therefore remains **Active / Tested**. This slice does not by itself justify promoting `PHIL-ASSURE-IMPL-CORR-001` to Implementation Refined.
