# FSEM-01 DATA-05B — two actual Surface eliminations for bounded nested source

**Proposed, non-normative, test-scoped correspondence.** Tracks [FSEM #1613](https://github.com/abiggerhammer/phil/issues/1613), the DATA-05 gap, R14/R15, and [DATA-05A](formal-semantics-nested-product-data05a-fsem01-v1.md). No production checker, native Core, grammar, TCB, assurance, compiler, ABI or P9 edits.

## Original source and conditional projection

The [strict source/Surface test](../../test/Phase1FSEM01Data05BSourceSurfaceMain.hs) reparses the 13 original DATA-05A Grammar-v1 fixtures. It reuses the established function/recursive-pattern lexical binder authority, resolves the exact source initializer and final returned binder, and independently typechecks every primitive leaf through grammarV1CheckedTypeMode. A **test-only two-level constructor** combines those checked leaves using the certified DataMode.productMode. This is **not** general production nested type elaboration.

The accepted right-nested original is:

~~~phil
fn unpack(packet : (Bool, (Bytes[8], Unit))) -> Bytes[8] satisfies C {
  let (flag, (payload, spare)) = packet;
  return payload;
}
~~~

There is a mirrored left-nested fixture as well. Both are flattened for test-only production Surface replay into two sequential **flat** tuple lets:

~~~text
let (flag, syntheticInner) = packet;
let (payload, spare) = syntheticInner;
return payload;
~~~

The mirror swaps positional outer successors. The packet, flag, payload and spare retain original declaration-rooted semantic identities and source spans. The distinct generated intermediate is an **internal Core name**, never claimed as an original source binder or an independently verified source elaboration. The test provides the two exact qualified product contracts in a test-scoped SurfaceEnvironment derived from its checked primitive leaves.

## Actual Surface and independent Core steps

The original-source test first independently executes native Core.insertBinding, two native DataMode.eliminateProductBinding calls and a one-shot Core.consumeLinear return, checking full original/outer/inner Map/Set states and no resurrection.

It then uses the **unchanged production traceSurfaceProductEliminationComponent** for the first flat let. The observed predecessor/post-state must equal independent native Core. A deliberately premature Bool return leaves a Linear intermediate, so the diagnostic prefix must fail LinearCompletion. That failure is not a post-error source successor.

A second production Surface trace, initialized with the previously checked exact native outer resource state, independently checks the second flat elimination and successful Linear Bytes[8] return. Finally, the complete three-statement test-projected component is checked by the ordinary production checkSurfaceComponent, and must agree with the successful second-stage result.

Hostile projected Surface negatives reject wrong/missing qualified outer/inner contracts, arity errors at either stage, duplicate or already-active successor identities, a stale consumed packet owner, and premature return of an Unrestricted Bool with live Linear debt. The original source fixtures retain their distinct lexical/type errors and out-of-adapter noncompetence; noncompetence is never called a normative invalidity judgment.

## Finite Rocq evidence and remaining authority

[SurfaceNestedProductSurfaceD05B.v](../../proof/Phil/Surface/SurfaceNestedProductSurfaceD05B.v) composes existing DataProduct and DATA-05A properties. It proves a missing first or second product restoration has **no two-stage model successor**; a successful two-stage finite projection has exact source-position arities and inner element mode/type, and two independently accepted plans can replay. The successful-step, exact type and identity premises remain explicit.

This is bounded original-source lexical/type observation to actual test-projected Surface checking and independent native Core agreement, **not** universal source-to-Core, Haskell-to-Rocq, compiler, or linked runtime refinement. It neither proves a general nested type rule, unrestricted tuple depth, arbitrary nested patterns, source satisfies-C, actual source-program execution, qualified provider law, nor FSEM-05/06 completion.

**COVERAGE-1 DATA-05 remains a gap.** Production nested Grammar-v1 type and pattern admission, generalized resource transitions and independent formal correspondence remain open. Focused CI compiles GHC 9.6.7 with -Wall -Werror, checks existing flat/DATA-05A regressions and Rocq 9.2 proof objects without new Axiom, Parameter or Admitted. Full exact-head PR CI, post-ready FSEM guard, protected expected-head squash and trusted release are separate merge gates.
