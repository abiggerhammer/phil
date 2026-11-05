# Phase 1 implementation-correspondence inventory v1

**Status:** Initial proposed coverage contract and evidence inventory for
`PHIL-ASSURE-IMPL-CORR-001`. This document does not change a Logic Ledger status.

**Evidence baseline:** `4abf85a7a469297e66c75671e9a877a5e597d9f5`
(2026-11-05). Source observations below refer to that revision. A later proof
slice must record its own exact revision and evidence before changing a row.

## Purpose and proposed scope

The umbrella target supplies the rule for connecting certified semantic claims
to production behavior. Its reusable rule is already demonstrated by the
[CALL-012 pilot](callable-implementation-refinement-v1.md):

`certified proposition -> executable sound/complete relation -> proved representation bridge -> extracted kernel -> byte-identical regeneration -> production acceptance path`.

This initial inventory has a deliberately finite scope: the Grammar-v1 parser
and AST correspondence dependency, plus two established implementation-binding
examples that fix the evidence standard. It is a seed for a complete coverage
manifest, not evidence that every compiler interface has been inventoried.

The proposed umbrella completion contract is: a versioned, finite list of
selected Phase 1 production interfaces, each connected to its stated certified
relation with the required implementation evidence and explicit residual
assumptions. Before claiming umbrella closure, finish that list, explain why it
covers the target's intended scope, and reconcile it with the current ledger.
Completing the parser dependency alone does not establish that coverage.

A Certified parent remains valid at its stated semantic scope. An existing
discharged implementation child can supply the production connection; a parent
is not a new open obligation merely because its status says Certified.
Primitive/runtime assumptions must be recorded at the boundary where they are
used. Naming a missing application decision as TCB does not satisfy its selected
implementation-refinement obligation.

Phase 1's charter and current ledger remain the authority for the phase exit
decision. This inventory proposes no whole-compiler verification requirement,
removal of the Haskell toolchain's trusted role, or change to Phase 1 semantics.
The [Phase 1 documentation guidance](README.md) also warns that historical
slice documents' old “not yet” lists are not a current backlog.

## Initial evidence inventory

These are local inventory labels, not new Logic Ledger target IDs.

| Entry | Observed evidence at the baseline | Exact boundary and remaining work |
| --- | --- | --- |
| G1: Grammar admission | `parseGrammarV1StructuralSource` in [Parser.hs](../../src/Phil/Surface/GrammarV1/Parser.hs) sends the canonical source tokens to `grammarV1ReferenceAcceptsSourceTokens` before running its handwritten parser. The [binding record](surface-parser-production-binding-v1.md) and rejecting-kernel control establish production dependence on certified admission. | Preserve this soundness connection. It supplies neither the converse acceptance implication nor universal fidelity of the returned `GrammarV1SourceFile`. |
| G2: Existing production representation adapters | The [source-header bridge](../../src/Phil/Surface/GrammarV1/ReferenceAstRepresentationBridge.hs) carries module/import information and declaration count. The [top-level bridge](../../src/Phil/Surface/GrammarV1/ReferenceAstTopLevelRepresentationBridge.hs) carries attributes and one of fifteen declaration tags. The [record/data bridge](../../src/Phil/Surface/GrammarV1/ReferenceAstRecordDataRepresentationBridge.hs) carries a compact projection. | These are intentionally bounded adapters. Top-level payloads are absent; the record/data bridge drops recursive type/proposition/effect contents and represents tuple payloads by arity. Full payload fidelity cannot be inferred from their round-trips or generated carrier identity. |
| G3: Formal record/data correspondence | [GrammarAstRecordDataShiftRefinedAdmissibleParseImplementation.v](../../proof/Phil/Surface/GrammarAstRecordDataShiftRefinedAdmissibleParseImplementation.v) proves that an observed successful reference parse of an admissible shift-refined record/data token stream has exactly one certified implementation carrier reconstructing that tree. | Retain the admissibility premise and carrier scope. This is a Rocq theorem about the formal carrier; it does not bind the Haskell AST builder or cover every Grammar-v1 declaration. Broader payload refinements need their own totality and correspondence proofs. |
| G4: Complete source AST comparison | [ReferenceAstWholeSource.hs](../../src/Phil/Surface/GrammarV1/ReferenceAstWholeSource.hs) defines `grammarV1ReferenceSourceCore` and `grammarV1ProductionSourceCore`. The [whole-source audit](surface-parser-ast-whole-source-correspondence-v1.md) covers all fifteen declaration families with complete normalized bodies and adversarial controls. | Finite corpus agreement is established as Tested evidence. Universal translation and the faithful connection to the actual production acceptance/output path remain the active dependency on `PHIL-SURFACE-GRAMMAR-CORR-001`. |
| C1: Callable refinement | The [CALL-012 pilot](callable-implementation-refinement-v1.md), [decision proof](../../proof/Phil/Core/CallableRefinementImplementation.v), and [incidence bridge](../../proof/Phil/Core/CallableRefinementImplementationBridge.v) connect the executable decision to the certified relation. [checkCallableRefinement](../../src/Phil/Core/CallableRefinement.hs) uses the extracted kernel and checks exact set round-trips. | Reuse this bounded proof/binding chain; do not reopen it because primitive equality or `Data.Set` remain named foundations. The final manifest must reference its existing ledger disposition and exact production evidence. |
| C2: Validity-scope matching | The [validity-scope closeout](assurance-validity-scope-implementation-refinement-v1.md) connects [Phil.Assurance.Verify.scopeMatches](../../src/Phil/Assurance/Verify.hs) to an extracted conjunction decision under `ScopeEntriesComplete` and `ScopeFactReflection`. Evidence, assumption, and export scopes use that function. | Reuse the existing `PHIL-ASSURE-VALIDITY-IMPL-001` child coverage. Record `Text` equality, finite map enumeration/lookup, and effective-context construction as explicit foundations, without claiming the Boolean kernel proves them. |

## Measurable completion criteria for the parser dependency

Close G1–G4 as a composed production claim only when the following evidence
exists for the declared token/AST domain. Full grammar-target closure requires
the normative Grammar-v1 domain; restricted milestones keep their narrower claim.

1. **Full reference translation.** Every certified complete Grammar-v1 parse
   has a translated, normalized AST. Cover all fifteen declaration alternatives
   and their recursive payloads; carry any remaining admissibility restrictions
   in the claim instead of calling a restricted result universal.
2. **Faithful representation.** State the exact equivalence between reference
   trees, formal carriers, and production ASTs. Prove the corresponding
   round-trip/correctness properties. Ignore spans and only explicitly
   documented syntactic distinctions; a projection that drops semantic
   payloads cannot witness full AST correspondence.
3. **Production behavior.** Bind the translation to the public parser through
   extraction or a mechanical behavioral-refinement proof. Prove successful
   production output matches the certified reference result and that
   certified-valid input in the declared domain can reach a corresponding
   successful production result. A rejection gate alone cannot establish
   that converse acceptance implication.
4. **Stable lexical boundary.** Preserve the canonical pre-normalization token
   convention and account for production compatibility normalization, including
   bare `Bytes`, in the correspondence. Do not silently change the language to
   make the bridge total.
5. **Revision-bound evidence.** Replay the relevant proofs; freshly regenerate
   extracted code; verify exact generated/production identity under the declared
   mirror policy; exercise the actual acceptance path and mismatch controls.
   Retain the whole-source corpus as regression evidence, alongside the
   universal proof rather than as its replacement.

A proof that adds a recursive payload carrier or reconstruction theorem advances
G3. It does not by itself close G2 or G4, establish production completeness, or
promote either active ledger target.

### Follow-up formal carrier evidence

The [recursive grouping slice](surface-parser-recursive-grouping-correspondence-v1.md)
merged in `9cf11bc88ff4b3d006e1f34336151b4ae7a30506` proves a lossless grouping
transformation and totality from a canonical grammar derivation using computed
tree-size fuel. Its command/fallback bodies remain explicit retained boundaries.

The subsequent
[primary/postfix composition slice](surface-parser-primary-postfix-recursive-grouping-v1.md)
uses that result to replace the actual tuple/parenthesized child fields in a
nine-alternative primary carrier, then embeds that replacement in the immediate
postfix consumer. It supplies exact reconstruction and grammar-derived totality,
including adapters for the existing carriers. Its named-postfix branch retains
the established representation. This is further formal evidence toward G3.

Based on that slice's merge, `a611f3d4c42647c1eb31831746b582078b14b900`, the
[arithmetic continuation](surface-parser-arithmetic-recursive-grouping-v1.md)
replaces the postfix leaf under recursive unary negation and every leading and
suffix operand through multiplication, addition, and shifts. It supplies
grammar-derived totality with computed fuel and exact reconstruction at each
layer.

Based on its merge, `9662568df0debc8ddcf6a0f8d3c7c14e2594c83c`, the
[expression continuation](surface-parser-expression-recursive-grouping-v1.md)
replaces the outer base-expression shift branch and uses that replacement in
both the main expression base and its separate reject-fallback operand. It
preserves optional absence/presence, commands, and failure targets, and supplies
exact reconstruction and derivation-only totality for the raw normalizers and
legacy adapters.

Based on the expression slice's merge, `bbfdfa9f19c3da4b52c248e6d80223d872bfbe84`,
the [term-argument continuation](surface-parser-term-arguments-recursive-grouping-v1.md)
replaces every expression in the selected outer argument list. Its exact
map-of-erasure equality preserves the complete list, including arity and order;
the shell/raw/legacy entry points have derivation-only totality. An empty list
denotes present `()` syntax, not an absent optional payload.

Based on the term-argument slice's merge, `bacf910a61786feed785de8f08fe3882ecbcdc2a`,
the [effect-expression continuation](surface-parser-effect-expression-recursive-grouping-v1.md)
replaces its optional term-argument payload with the complete-list carrier.
It preserves absent arguments versus present empty `()`, reconstructs the exact
old shallow carrier and tree, and directly preserves the complete static-reference
carrier in the legacy adapter. All public totalities require only the relevant
grammar derivation.

Based on the effect-expression slice's merge,
`838cd27598edf23aa43d5e1a7b3251e45b489a8e`, the
[effect-set continuation](surface-parser-effect-set-recursive-grouping-v1.md)
replaces every literal member with that effect carrier and preserves the
enclosing literal/reference choice. Raw and direct legacy list traversals
preserve count, order, multiplicity, and complete member erasure. All six
literal/choice shell, raw-tree, and legacy totalities require only the relevant
grammar derivation. The next selected consumer is the effect-set field in the
`effects ... within ...` generic-requirement alternative (index 6), followed by
the established record/data route. Static-reference argument interiors,
named-postfix argument payloads, command bodies, failure-target arguments,
the generic grouping carrier's nested fallback boundary, and production AST
binding retain their separate obligations.
These local carrier results do not close G2 or G4 or promote an umbrella target.

## Work needed to finish the umbrella inventory

The next inventory pass must make coverage reviewable before an umbrella
closeout is attempted:

- Enumerate the selected authority-bearing acceptance/translation entry points
  and their exact input/output domains. Give each an existing ledger claim or
  implementation child, certified relation, executable decision/translation,
  representation bridge, and production caller.
- For each entry, record one evidence disposition: an existing completed bounded
  implementation claim, an identified proof/binding gap, or an explicit
  exclusion from the proposed scope. Record native foundations separately;
  they are assumptions of the evidence, not a substitute for a missing proof.
- Reconcile the list against the current Logic Ledger and relevant conformance
  cases. Reuse discharged child coverage and identify any genuinely unmapped
  production path. This initial document does not assert that G1–G4 are the
  only remaining gaps.
- State the aggregate claim and scope after that reconciliation. Only then can
  the list serve as a finite closure checklist for
  `PHIL-ASSURE-IMPL-CORR-001`.

Each completed entry must identify the exact production revision, theorem and
source identities, extraction/bridge identities, workflow evidence, and retained
assumptions. The [Rocq certification profile](../assurance/rocq-proof-certification.md)
distinguishes compiling a proof from attaching selected certificate authority;
source hashes and green tests alone do not establish behavioral correspondence.

## Native foundations and change discipline

Existing examples retain GHC/runtime and Rocq extraction trust, concrete
`Text` equality, and selected `Map`/`Set` behavior. The
[assurance evidence binding](assurance-evidence-authority-production-binding-v1.md)
also distinguishes its gate from trusted-artifact lookup, runtime-mechanism
truth, and external evidence truth. Record these assumptions beside the
particular claim that uses them; do not describe them as newly discovered
Phase 1 feature gaps.

Keep this proof inventory separate from implementation-audit remediation.
Any discovered mismatch belongs in its own concrete issue or proof obligation;
this document neither repairs such mismatches nor changes their disposition.
