# R19: selected entries must match semantic qualification

## Review and implementation scope

This remediation addresses R19 in the 20 September 2026 implementation-audit
continuation at `2b0e9982240b4b8d9a1a7a24cc4850be4cb5d331`. Its implementation
base is `f2ed3c158b229a67320d7518e3e3f51fb289605c`, after the R3 block-coverage
repair in PR #1242. The review report is preserved in the Phase 1 Code Reviews
folder as **Phil code review — continuation — 2026-09-20 — 2b0e998.md**.

The provider stage already checks that each represented link agrees with the
candidate's selected operation-to-entry map. That check cannot authorize a
coordinated change to both descriptions. The authority/effect stage has the
genuine semantic qualification but previously checked only the operation key,
not `checkedProviderImplementationEntry`.

`checkQualifiedEntry` now takes a concrete
`Map ProviderOperationKey ProviderImplementationEntryKey`. For each qualified
operation it requires both the correct operation key and equality of the
selected entry with the checked implementation entry. A mismatch reports the
existing `AuthorityEffectOperationEntryMismatch occurrence operation`.

The preceding exact operation-domain check remains in place, so this covers
the full selected map, including qualified operations with no represented use
in an intentionally relative subset. Both `verifyAuthorityEffectStageBundle`
and `verifyAuthorityEffectStageBundleAgainst` execute this check. No public API
signature, revision format, opaque-provider rule, effect/authority assignment,
or lower provider-only verifier is changed.

## Regression corpus

`test/Phase1ReviewR19QualifiedEntryMain.hs` has eleven cases:

1. Genuine Steve qualification through the strong authority/effect gate.
2. The opaque Upload witness through its strong gate.
3. Link-only entry mutation, rejected by the existing provider-base diagnostic.
4. Selection-only entry mutation, rejected by the existing provider-base diagnostic.
5. A characterization control: the complete provider-only gate still accepts
   coordinated rebinding because it lacks semantic qualification authority.
6. Coordinated digest.compute-to-digest.check entry rebinding rejected at the
   strong authority/effect gate.
7. The same coordinated rebinding rejected at the relative authority/effect gate.
8. Reverse digest.check-to-digest.compute entry rebinding rejected at the strong gate.
9. Blob read-to-install entry rebinding rejected at the strong gate.
10. A selected-but-unused operation rejected for its wrong qualified entry,
    after a genuine relative-subset acceptance control.
11. Restoration of the genuine mapping recovers exact original stage identity
    and strong-gate acceptance.

Original and donor entries are obtained from freshly materialized genuine
qualifications and must differ. No checked qualification is forged or changed.
The coordinated cases keep independent occurrence/operation expectations, the
complete site inventory, admission and claim inputs, semantic surfaces,
authority/effect uses, runtime symbols/signatures, and Subject/Systems content
fixed. Both stage revisions are rebuilt and checked. Restoring only the two
entry descriptions must recover the entire original bundle exactly.

The unused-operation test deliberately uses the relative API: omission of a
site there is not claimed to satisfy independent inventory completeness. Its
purpose is to show that even an unused selected operation must match its
qualification. Existing R14 deletion and complete-erasure controls remain.

## CI and assurance boundary

The existing **Phase 1 Review R14 Provider Call Inventory** workflow now
strict-typechecks and executes the R19 corpus with GHC 9.6.7, then retains its
R14, R13, provider-correspondence and authority/effect controls. Its path filters
include the new test and its production/fixture dependencies. No parallel
workflow or Cabal component is introduced.

At authoring this code is submitted for CI. There is no local GHC or Cabal
installation, and no local execution of the old or repaired Haskell candidate
is claimed. Exact-head CI and independent audit closeout remain necessary.

The repair does not turn raw `Checked...` records into opaque capabilities or
re-prove their originating qualification checker. It checks correspondence
against the supplied genuine qualification at the existing trust boundary.
Proof sources, generated kernels, and Certified ledger status are unchanged;
existing extracted-kernel claims are not expanded to cover this new native
comparison without a separate proof/refinement closeout.

R13/R14-C1 remains separate: BranchResource and StageClosure still need the
independent complete provider expectation inventory propagated through the
actual cumulative consumer route. This slice repairs qualified entry equality;
it does not claim cumulative provider-call completeness, native execution of
an alternate implementation, or full R19 audit closure before CI/re-review.
