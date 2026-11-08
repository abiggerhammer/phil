# FSEM-01 — source-checked nominal affine and linear product return

> **Status:** bounded, non-normative, exact production-checker source witness.
> Tracks issue [#1613](https://github.com/abiggerhammer/phil/issues/1613)
> following [#1667](https://github.com/abiggerhammer/phil/pull/1667).
> The product uses an explicitly admitted external lifecycle justification.
> Neither source text nor a caller-provided resolver record is itself a proof.

## One admitted source example

~~~phil
data Permit mode affine = Permit(U64);
fn use(permit : Permit, payload : Bytes[8]) -> (Permit, Bytes[8]) satisfies C {
  borrow permit as view { view; unit; };
  return (permit, payload);
}
~~~

The existing nominal data-mode checker first checks the closed Permit data
declaration with an externally **admitted** lifecycle obligation. Absent or
unadmitted obligations reject strengthening an unrestricted U64 payload to
Affine. A data declaration may not weaken Linear Bytes[8] to Unrestricted.

The function's two parameter types then run through the existing nominal
resolution checker with exact GenericTypeKind, DeclarationKey and
InterfaceRevision identity. The two parameter binders share a single
source-rooted lexical scope. The first one checks as Affine TyOpaque Permit;
the second checks independently as intrinsic Linear TyBytes 8.

The new **opt-in** checked flat-product resolver in
[CheckedType.hs](../../src/Phil/Surface/GrammarV1/CheckedType.hs) admits bare
nominal elements only through an exact supplied name/kind/declaration/interface
resolution. It retains the provenance of each member and yields the ordered
TyProduct element contracts and derived Linear aggregate mode. Missing,
wrong-kind, ambiguous and incompatible semantic-type resolutions are all
rejected. The existing primitive-only generic flat-product route is unchanged,
including its unsupported nested/nominal behavior.

[SourceAffineProduct.hs](../../src/Phil/Surface/GrammarV1/SourceAffineProduct.hs)
recognizes precisely one nonrecursive, non-generic two-parameter function with
one lexical borrow of the affine Permit and one two-member tuple return.
It projects exact source-resolved binder identities, not display spellings,
into a **single real production Surface checker execution**. The checked
source product contract becomes surfaceExpectedProductReturn; the actual
runtime tuple must match every ordered type and mode. The regular and traced
production checker outcomes are required to agree. Unrecognized source shapes
return non-competence rather than receiving an opaque fallback.

## Executable positive and negative controls

[Native Haskell regression](../../test/Phase1FSEM01NominalAffineProductMain.hs)
parses 13 files in
[the nominal-product corpus](../../test/fixtures/fsem01-nominal-affine-product-v1)
and verifies exact production outcomes:

- **accepted:** the affine Permit is borrowed, then the loan is closed;
  returning (Permit, Bytes[8]) moves both owners exactly once and checks the
  exact ordered affine/linear TyProduct. Four-zone production checkpoints
  agree with independent native Core start/end/consume operations; all
  structural maps and loans are empty after return.
- **reversed, wrong-width, wrong-mode:** source-declared product and actual
  runtime tuple disagree, producing the exact production TypeMismatch detail.
  The error path does not invent a successful return checkpoint.
- **duplicate-affine, duplicate-linear:** the same restricted semantic binder
  is moved twice, producing StructuralUse rejection and no return successor.
- **escape:** removing the final unit expression from the borrow body yields
  exactly BorrowEscape and a terminal error prefix; the loan remains active
  and both owners remain present.
- **unjustified, weakened:** missing/unadmitted external lifecycle authority
  and an explicitly weakened data-mode declaration reject through existing
  nominal checks.
- **unknown-named:** the nominal return element has no resolution and is
  rejected rather than receiving an invented structural mode.
- **nested, wrong-arity, wrong-borrow:** outside this bounded source adapter's
  competence; no generic fallback is inferred.

Additional adversarial tests exercise unresolved, wrong-kind, ambiguous and
wrong-typed named resolver entries. The resolver's declaration and revision
values are explicitly **caller-supplied premises**, not independently
authenticated lineage objects.

## Machine-checked Rocq model slice

[SurfaceNominalAffineProductBridge.v](../../proof/Phil/Surface/SurfaceNominalAffineProductBridge.v)
composes the existing flat-product correspondence and finite-context
ownership theorems. The conditional lemmas establish:

1. The affine/linear ordered product has Linear aggregate mode.
2. Source nominal admission entails the explicit external admission Boolean.
3. Conditional on sound Ty equality, exact product matching preserves
   ordered element types, modes and arity.
4. Reordered elements or an incorrect affine/linear element mode reject.
5. A modeled affine consumption followed by a linear consumption removes
   both owners exactly, while preserving all unrelated binding/loan lookups.

The reference model has abstract Rocq Ty and String identifiers. It is
**not** universal native Haskell Data.Map/Data.Set/Unicode equivalence;
a sound equality premise is not an implementation proof. Successful finite
source witnesses are tested against the actual production checker but
Haskell-to-Rocq transition simulation, native exact-error refinement and
source type soundness remain open. No new admitted theorem or axiom is added.

## CI and remaining scope

[The focused early preflight](../../.github/workflows/fsem01-nominal-affine-product-preflight.yml)
is scoped to the dedicated work branch and then this PR. It checks a
-Werror production Haskell library build, the established SURF-008 and
FSEM-01 regression drivers, this new source test, Rocq 9.2 compilation,
Print Assumptions, and a no-new-admissions gate. Full exact-head PR CI and
a fresh FSEM claim guard are separately required before merging.

**Not claimed:** general recursive/nested products, constructors/elimination,
multiple declared nominal types, arbitrary borrow expressions, joins/loops,
captures, complete satisfies C discharge, general source-to-Core preservation,
whole-compiler correctness, or an independently executable Rocq reference
interpreter (FSEM-05). An exact finite witness cannot graduate a rule to
normative authority by itself.
