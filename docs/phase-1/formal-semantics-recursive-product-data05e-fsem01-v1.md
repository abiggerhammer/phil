# FSEM-01 DATA-04/05E — source-owned recursive binary product trees

**Non-normative bounded competence.** Tracks [#1914](https://github.com/abiggerhammer/phil/issues/1914)
and parent [#1613](https://github.com/abiggerhammer/phil/issues/1613).
Builds on [DATA-05C #1864](https://github.com/abiggerhammer/phil/pull/1864)
and [DATA-05D #1910](https://github.com/abiggerhammer/phil/pull/1910).
Neither earlier production adapter is modified; the new recursive module is
separately registered in phil-core.cabal.

## Admitted source domain

An original parsed nonrecursive, nongeneric Grammar-v1 function with
exactly one parameter, one matching source tuple-let pattern and final
source-local return. Tuples are *finite binary trees of any height/shape*,
including two nested children at the same parent. Permitted checked
intrinsic leaves are Unit, Bool, U<n> and Bytes[N]. Exactly **one**
Linear Bytes[N] leaf must be returned; all other leaves must be
Unrestricted. A name-only identifier pattern over a product, flat
arity-3 syntax, nominal alias, named recursive type, proof/refinement,
record/sum, multiple Linear leaf, generic or unsupported body is
**noncompetence** or an exact scoped source-check failure as applicable;
it is never silently equated to invalid *normative* source.

The original declaration root determines each actual lexical binder's
semantic Core Name. Product-tree shape and mode/type are computed
*structurally recursively* from checked source types and matched
source patterns. A path-encoded internal Core name is generated only
for each nested intermediate product; collision-freedom is checked
against **all** original source leaf names and generated names.

## Production Haskell/Core/Surface evidence

The new opt-in module
[SourceRecursiveProductElimination.hs](../../src/Phil/Surface/GrammarV1/SourceRecursiveProductElimination.hs)
takes **only** StaticContext, DeclarationKey and original function AST.
No caller-authored SurfaceEnvironment, privileged product contract,
synthetic source binder or external lifecycle evidence is accepted.

A structural recursive preorder generates one flat product elimination
for each internal node. The native production
Core.DataMode.eliminateProductBinding executes every exact step; the
unchanged production Surface
traceSurfaceProductEliminationComponent observes actual four-zone
before/after Map/Set states and must agree with independent Core
native replay, including at leaves of *both* nested branches. Each
single-step diagnostic Unit prefix must reject on exact LinearCompletion;
the full source-derived component must consume and return the unique
Bytes[N] Linear owner exactly once, leaving no unpaid Linear debt.
An Unrestricted-only product can legitimately remain reusable after
elimination; the non-resurrection property applies to **restricted**
owner identities. No successful state is invented after native or
Surface failure.

The test
[Phase1FSEM01Data05ERecursiveProductMain.hs](../../test/Phase1FSEM01Data05ERecursiveProductMain.hs)
parses actual .phil fixtures of depth 1, 2, 3, 4+ and two-sided
nesting, including U8 and Bytes[8]/[16]/[32], and independently
executes every Core elimination. Source negatives isolate wrong
return/width/pattern, two Linear leaves, duplicate/shadow source
binder, unsupported alias/arity/source reference and multi-statement
noncompetence. Declaration roots and alpha-renaming are checked.

## Kernel model and authority limits

[SurfaceRecursiveProductSourceD05E.v](../../proof/Phil/Surface/SurfaceRecursiveProductSourceD05E.v)
defines an **inductive** finite binary product tree with recursive
accepted-plans and preorder replay, proving (by structural induction)
that every accepted tree replays with exactly the tree's stage count,
and that failure at a root or either recursive child forbids a
fabricated successful successor. It proves every realized root stage
has the exact ordered successor type/mode/name contract.
This is a **conditional Rocq model**, not a theorem that the actual
Haskell checker refines it for all programs. Tree-to-source semantic
representation, globally distinct names, ordinary Haskell
Map/Set/Text behavior and actual native execution are separate
source/evidence premises or finite conformance checks; no new axiom,
Parameter or Admitted is introduced.

**Nonclaims:** Not all admitted Grammar-v1 products, multi-Linear
return/disposition, nominal/recursive/record/sum/alias/dependent types,
all lifecycle/assurance or satisfies C obligations, FSEM-05 reference
execution, FSEM-06 implementation refinement, P8/P9/P10 authority,
or FSEM-01 exit. DATA-04/05 and R14/R15 remain **general** gaps.

This slice must not edit shared P9 Engine.hs, accepted grammar,
privileged/release/TCB, FSEM-02 or assurance/provider code. Strict
GHC9.6.7 (-Wall -Werror) and Rocq9.2 focused preflight are required
*before* a draft PR, followed by full exact-head checks and the
fresh post-ready claim guard before any protected squash/claim release.
