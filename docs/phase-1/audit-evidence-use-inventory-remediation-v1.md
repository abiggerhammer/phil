# Phase 1 audit remediation: actual evidence-use inventory

This implementation-side remediation continues the defensive `D-RES-SUPPORT-01` / `D-RES-TREE-01` correspondence chain after the original-event preservation repair.

## Boundary

The proof-side correspondence now requires the native implementation to start from the complete evidence-use domain actually returned by the checker, rather than from a caller-selected subset:

`actual evidence use -> subject-bearing use OR checked closed use`

`actualEvidenceUseInventory` derives that inventory directly from `ValueResult.valueResultEvidence`. Callers do not supply a selected evidence set.

For a subject-bearing use, the adapter records every `RefVar` occurrence in the proposition carried by the actual `EvidenceUse`, in deterministic left-to-right order. Equal names are deliberately not deduplicated. This preserves the information needed for later occurrence-level semantic-subject correspondence, including multi-subject facts and repeated occurrences of one subject.

For a checked-closed use, the adapter requires the actual evidence proposition itself to contain no `RefVar` occurrence. Missing endpoint metadata, missing map entries, source spelling, type equality, or normalization to `Truth` are not used as evidence of closedness. In particular, a definitionally true proposition such as `x == x` remains subject-bearing because the actual checked evidence still names `x`.

## Ownership separation

This inventory is logical evidence metadata only. It reads the returned `ValueResult` and never edits its `CheckState` or resource context. A consumed affine or linear owner therefore remains consumed even when an evidence proposition retains the logical occurrence of that subject.

## Required controls

The permanent regression covers:

- a genuinely closed literal evidence use classified as checked closed;
- a definitionally discharged `x == x` retaining both subject occurrences rather than disappearing through normalization;
- actual carried `EvidenceByBinding` remaining subject-bearing;
- an actual residual evidence use being inventoried;
- a multi-subject residual retaining every subject occurrence and order;
- exact one-based inventory coverage of every evidence use returned by a real checker result; and
- a consumed linear owner remaining absent while its logical evidence occurrence remains represented.

## Deliberate non-claims

This slice does not assign semantic endpoint IDs, infer occurrence identity from a `Name`, prove a stable-subject or checked-rebase relation, or bind evidence to a final consuming operation. It also does not manufacture an original event identity for a residual-free `ValueResult` merely because some caller has a `ResidualSpec`.

Those remain subsequent correspondence boundaries:

`complete actual-use/occurrence inventory -> competent semantic endpoints -> stable subject or checked rebase -> same original event -> actual final consumer use`.

Direct immutable named-evidence authority and certificate fact authority remain on their existing fail-closed paths. No Rocq/proof source is changed by this remediation, and LLVM remains inside the Phase 1 trusted computing base.
