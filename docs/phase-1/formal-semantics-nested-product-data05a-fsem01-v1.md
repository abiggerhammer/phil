# FSEM-01 DATA-05A — source-derived nested tuple ownership foundation

**Proposed, bounded, non-normative.** Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613), the DATA-05 gap in [COVERAGE-1](formal-semantics-fsem01-coverage1-v1.md), and exit-matrix R14/R15. No production Haskell, grammar, accepted TCB, assurance, compiler, or runtime change.

## Source fragment and lexical authority

The test-scoped adapter [Phase1FSEM01Data05ANestedProductMain.hs](../../test/Phase1FSEM01Data05ANestedProductMain.hs) admits two original Grammar-v1 functions with mirrored nesting:

~~~phil
fn unpack(packet : (Bool, (Bytes[8], Unit))) -> Bytes[8] satisfies C {
  let (flag, (payload, spare)) = packet;
  return payload;
}
~~~

The mirror puts the nested pair on the left. The real structural parser, existing function/pattern binder scope, exact lexical return occurrence, and established primitive type/mode checker supply the source facts. **A separate, test-only recursive walker** composes the primitive checked leaves into a nested Core product type using the existing certified product mode function. This is NOT production nested type elaboration or acceptance by the ordinary Surface checker, and it does not discharge satisfies C.

Both the original and the intermediate product have Linear mode because the inner pair contains Linear Bytes[8]. The intermediate is a fresh synthetic Core name derived from the actual source owner, not a source binder. A fully Unrestricted intermediate would not satisfy the one-shot premise and is deliberately excluded.

## Actual two-stage Core operations

Given the original source-derived packet name, the driver executes actual Core.insertBinding followed by two separate DataMode.eliminateProductBinding transitions. The first consumes the outer Linear product and restores a Bool and one Linear inner product. The second consumes the inner Linear product and restores the Bytes[8] and Unit leaves. The final Core.consumeLinear returns the Bytes owner once, and Core.ensureComplete certifies no remaining loan or Linear debt.

Exact native Map/Set snapshots are checked after each stage. The original packet, intermediate and returned Bytes owner are independently tested for stale-use refusal. Additional exact native negatives include wrong outer/inner arity, duplicate successors, collisions with another live binding, wrong product type/mode, live loan on the intermediate, and premature Linear completion. No test manufactures a successful source-level Surface elaboration.

[The 13 original source fixtures](../../test/fixtures/fsem01-data05a-nested-product-v1/) cover two admitted orientation witnesses, duplicate source names, active shadowing, wrong returned identity/type, wrong width/leaf type, mismatched pattern orientation, and four clearly out-of-adapter examples (wide/flat pattern, unknown return, extra statement). Adapter noncompetence is not a normative invalid-source verdict.

## Conditional Rocq and explicit residual

[The Rocq foundation](../../proof/Phil/Surface/SurfaceNestedProductFoundationD05A.v) composes existing DataProduct positional restoration and Context Linear consumption laws. It proves conditional two-stage positional preservation, independent arity/uniqueness, no fabricated inner leaf contracts, nested Linear mode, and no resurrection of distinct outer/inner Linear owners. This finite extensional model requires explicit type/identity/transition premises; it is not universal Haskell Map/Set/Text-to-Rocq refinement or general source-to-Core nested product preservation.

Focused CI uses GHC 9.6.7 with -Wall -Werror and Rocq 9.2.0, with original flat product regression tests and no new axiom/admission. Merge must require all exact-head PR checks, fresh post-ready FSEM claim guard, protected expected-head squash and trusted claim release.

**DATA-05 remains a gap**, because ordinary production Surface nested tuple acceptance, recursion/dependency/general product elimination, FSEM-05/06/07, assurance and Phase-1 freeze are not established. This slice avoids every P9 selected-provider/assurance/ABI/Engine site and the separate FSEM-02 lane.
