# FSEM-01 — exact Grammar-v1 borrow identities in the production loan checker

> **Status: bounded implementation/correspondence slice, not a normative
> language-wide type-soundness or compilation theorem.** This follows the
> [FSEM-01 lexical control](formal-semantics-borrow-scope-fsem01-v0.md)
> and the [formalization track](https://github.com/abiggerhammer/phil/issues/1613).

## Purpose and admitted source shape

This slice connects a *parsed Grammar-v1 function declaration* with an
**intrinsically linear** \`Bytes[N]\` term parameter to the **existing**
production surface/resource checker. It uses:

- [CheckedType.grammarV1CheckedTypeMode](../../src/Phil/Surface/GrammarV1/CheckedType.hs)
  to derive the intrinsic \`Linear\` mode and exact \`TyBytes\` value from the
  source parameter and result types independently (no caller-invented mode);
- [BinderScope](../../src/Phil/Surface/GrammarV1/BinderScope.hs) and
  [BorrowViewScope](../../src/Phil/Surface/GrammarV1/BorrowViewScope.hs)
  for identity-bearing owner and child-loan view binders;
- [BorrowResourceSurface](../../src/Phil/Surface/GrammarV1/BorrowResourceSurface.hs)
  for the *bounded* source-to-legacy checker projection, using generated
  Core names, not author-facing spelling;
- [Surface.Check.Engine.checkSurfaceComponent](../../src/Phil/Surface/Check/Engine.hs)
  and its existing \`evalBorrow\` implementation, including the real
  \`startSharedLoan\`, \`endSharedLoan\`, and \`BorrowEscape\` pathways.

The admitted test family consists of source functions shaped like:

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { (); };
  return owner;
}
~~~

The owner/result type is checked as the *same exact* \`TyBytes(8)\`, and the
owner is returned **only after** the loan is ended. Successful production
checking must report terminal \`Return TyBytes(8)\`; failure cannot be
relabelled as source acceptance.

**The escaping-view negative** differs only in the loan body's result:

~~~phil
fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {
  borrow owner as view { view; };
  return owner;
}
~~~

Both declarations have identical parameter and return types and identical
outer \`return owner\`. The negative's final loan-body expression returns
the view itself; the checker must report **\`BorrowEscape\`**, specifically
"shared view escapes its lexical scope", from the production loan-checking
path. A second positive uses \`{ view; (); }\` to demonstrate that a
temporary view observation may be discarded *inside* the borrow scope
before a Unit result closes the loan.

## Guardrails and correspondence boundary

- This is a **bounded source fragment** and accepts exactly one linear
  intrinsic \`Bytes[N]\` owner parameter, a single borrow-expression
  statement with supported scoped expressions, and an exact owner
  return. It **does not** provide a general implementation of function
  bodies, records, captures, proof obligations, provider invocation,
  nested borrows or arbitrary name/qualified-global lookup.
- Unsupported source forms produce explicit non-competence (\`Nothing\`);
  they are not accepted as valid and do not get synthesized types or
  invented static references. Named/opaque type modes are not guessed.
- \`satisfies C\` is source syntax retained by parsing but **not
  discharged** by this body projection. No blanket statement about
  selected architecture or source-level certification follows.
- \`GrammarV1CheckedLetUnitStep\` extends the existing lexical trace
  only to an exact Unit expression statement; all other unsupported
  expression forms still remain non-competent.
- The actual production borrow checker owns temporary-view result
  escape, linear owner consumption and loan closure; the adapter is
  not an alternative resource checker.
- The proof-side [ResourceScope.v](../../proof/Phil/Core/ResourceScope.v)
  theorem is about a normalized *continuing-boundary* projection,
  not yet an established proof that the complete Grammar-v1 source
  elaborator preserves that model's resource/loan semantics.

## Executable evidence

[\`test/Phase1FSEM01BorrowResourceMain.hs\`](../../test/Phase1FSEM01BorrowResourceMain.hs)
tests:

1. Legal \`Bytes[8]\` owner with Unit borrow body, followed by exact return.
2. Legal local use of \`view\` followed by Unit, then owner return.
3. A loan-body result \`view\` rejected by the production \`BorrowEscape\`
   class and its exact diagnostic (not \`TypeMismatch\`).
4. Unrestricted \`U8\` owner rejected as outside this linear-only route.
5. Unresolved owner spelling cannot acquire an invented static/global binding.
6. Borrow view cannot shadow its original owner identity.

The [borrow-view scope workflow](../../.github/workflows/phase1-surface-borrow-view-scope-proofs.yml)
strictly typechecks the adapter and replays the above tests. CI evidence
must be assessed on the **exact final PR head**, and a passing test
does not upgrade this bounded source fragment into global correctness.

## Next soundness obligations

1. Extend the trusted body projection with explicit provenance for
   all supported owner/loan types and effectful paths, without changing
   the language semantics.
2. Show that every admitted source binder, type and borrow action maps
   to the **same** production checker resource identity and mode,
   rather than merely agreeing on tested examples.
3. State an explicit source-to-resource-state simulation/refinement
   relation and prove the relevant correspondence to the normalized
   loan model; record the actual obligation in the Logic Ledger.
4. Separate lexical use-after-scope errors from possible static/global
   resolution, and expand full typed-source negative diagnostics only
   where the implementation has that competence.
5. Include checked joins, loops, captures, nested view aliases, and
   failure/terminal paths in subsequent slices.

The central result of this PR, if CI passes, is deliberately concrete:
**one source-derived linear borrow can be checked using the existing
production loan machinery, and a genuine escaping result is rejected
with the production error class.**
