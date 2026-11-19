# FSEM-01 DATA-04/05D — bounded three-level source-owned product elimination

**Non-normative, single-shape implementation evidence; not FSEM-01 closure.**
Track [#1908](https://github.com/abiggerhammer/phil/issues/1908),
parent [#1613](https://github.com/abiggerhammer/phil/issues/1613),
historical [DATA-05C #1864](https://github.com/abiggerhammer/phil/pull/1864)
and merged [closeout #1907](https://github.com/abiggerhammer/phil/pull/1907).

## Original source and checked authority boundary

The original parsed Grammar-v1 function is nonrecursive, nongeneric,
has one source packet owner, one three-level nested tuple let, and returns
exactly the original checked Linear Bytes[8] payload:

```phil
fn unpack(packet : (Bool, (Unit, (Bytes[8], Unit)))) -> Bytes[8] satisfies C {
  let (flag, (before, (payload, after))) = packet;
  return payload;
}
```

Each original primitive leaf is checked by the existing production
Grammar-v1 type/mode checker, each source binder identity by the existing
declaration-rooted lexical checker. The added independent entry point in
[SourceNestedProductElimination.hs](../../src/Phil/Surface/GrammarV1/SourceNestedProductElimination.hs)
takes only StaticContext, DeclarationKey and the checked original function
AST. No caller supplies a SurfaceEnvironment, product contract or generated
Core identity. Unsupported forms return explicit Maybe noncompetence
rather than a global invalid-source verdict; DATA-05C remains unchanged.

The source-owned adapter generates two distinct internal Core owners and
derives three ordered product contracts, then reuses the unchanged actual
production Surface checker for three staged eliminations. All actual
before/after native Map/Set resource-state cuts match independently computed
Core operations. The first two diagnostic partial returns must fail exactly
at LinearCompletion; the final full projected component returns one Linear
Bytes[8] with no retained Linear debt or resurrected intermediate owner.

## Evidence and proof boundaries

[Native/source test](../../test/Phase1FSEM01Data05DSourceAdmissionMain.hs)
reparses the original admitted/minimally rejected .phil fixtures, compares
independent real Core DataMode.eliminateProductBinding stages, checks precise
source-negative classes, error-prefix results, alpha-renamed binder keys
and independent declaration-root Core identities. No caller-authored
provenance or fake raw-source certificate is accepted.

[Conditional Rocq model](../../proof/Phil/Surface/SurfaceNestedProductSourceD05D.v)
proves valid three-stage plans replay, missing first/second/third plans have
no fabricated successful final successor, exact plan arity, and unchanged
final ordered element mode/type/name under stated model premises. Native
Haskell ↔ Rocq implementation correspondence remains unproved. No new
Axiom, Parameter or Admitted. Focused CI uses strict GHC 9.6.7
-Wall -Werror for production and checked source/native tests and Rocq 9.2.

**Nonclaims:** not arbitrary recursive/general nested products, record/sum
destructuring, dependent modes, full original source-byte authentication,
satisfies C assurance discharge, FSEM-05 runtime execution, FSEM-06 target
realization, a universal Haskell/Rocq refinement, P8/P9/P10 authority,
or Phase 1 freeze. DATA-04/05, R14/R15 and FSEM-01 remain general gaps.

Do not modify shared P9-owned Engine.hs or FSEM-02, accepted normative
grammar, TCB or privileged/release workflows. Exact-head PR CI, fresh
post-ready claim guard, protected expected-head squash and exact trusted
claim release remain required, regardless of focused preflight success.
