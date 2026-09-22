# PHIL-AUD-BRANCH-EVIDENCE-CAPTURE-001 — proof remediation staging

This tranche addresses the proof gap identified by the 22 September branch-evidence audit. It does **not** modify production Haskell.

## Missing property

The existing ContextJoin proof establishes equality/intersection properties of supplied resource maps. The existing Focusing proof classifies a requirement after matching evidence has already been supplied.

Neither model establishes that a concrete proof/type which leaves a branch still refers to the same logical subject after:

- the branch-local binding is pruned;
- the returned value is rebound in the parent;
- two arms are joined; and
- a later binding reuses the same source spelling.

The audit counterexample is therefore not a contradiction of either existing theorem. It is a missing subject-support correspondence relation.

## Normalized subject model

`BranchEvidenceSupport.v` separates **logical subject identity** from source spelling.

A small binder-aware `SubjectFormula` model computes free logical-subject support. `SubjectBind` extends the bound-subject set, and `formula_support_excludes_bound_subjects` proves that subjects already bound at a point do not appear in that formula's free support.

Source spellings are intentionally absent from `SubjectId`. Reusing the same display name later cannot by itself recreate an old logical subject.

## Scope export

A supported subject may cross scope exit in exactly two ways:

1. its logical subject is still live in the surviving environment; or
2. an explicit checked rebase maps the local subject to a surviving logical subject.

`ExportSupport` lifts that relation across every subject dependency of the escaping type/evidence.

The proof establishes:

- every exported subject is present in the surviving subject set;
- a removed subject with no rebase cannot export;
- adding a distinct fresh subject later cannot make that removed subject export;
- an explicit checked rebase can preserve an alias relationship to a surviving outer subject.

This directly captures the audit's same-spelling-reuse requirement: later lexical reuse is harmless because fresh allocation has a different logical identity.

## Branch join

`BranchSupportJoin` requires both arms to export to **the same logical support** before a result can be joined.

Consequences proved here:

- joined support consists only of surviving subjects;
- closed results join without subject support;
- independently local branch subjects may join after each is explicitly rebased to the same surviving outer subject; and
- an unsupported local subject cannot participate in a branch join merely because the other arm has textually matching syntax.

## Deliberate staging boundary

This is the semantic/proof tranche, not yet production correspondence.

A successor must bind this model to the concrete production chain named by the audit:

- binder-aware support over real `Ty`, `Proposition`, session continuations and residual obligations;
- `checkScopedValueBlock` / `pruneScopedPath`;
- `bindPattern`;
- `joinExclusive` / `joinMetadata`; and
- evidence/value consumers such as `findMatchingEvidence`, `findFocusedEvidence`, `checkValue`, and `accept`.

The implementation may use durable logical IDs, a checked export/rebase relation, or reject unsupported extrusion. It must retain positive closed/refined/owning branch results and must not restore consumed owners.

Because no production repair for this finding has landed yet, this PR deliberately does not extract a Haskell kernel or claim production binding. Once the Haskell remediation exists, a separate correspondence tranche can choose the exact executable boundary rather than guessing it in advance.
