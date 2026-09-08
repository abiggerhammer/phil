# Phase 1 portable negative corpus

This directory begins the INT-004 migration from implementation-private negative tests to portable conformance fixtures.

`manifest.tsv` is normative for the migrated frozen Phase-0 semantic negatives. Each row gives a stable fixture identity, portable `.phil` input path, implementation-independent rejection class label, earliest competent rejection layer, explicit environment profile name, and governing Matrix authority.

The portable replay selects its checker environment by the manifest's stable `environment_profile` field through `Phil.Surface.Phase0.phase0EnvironmentProfile`; fixture filenames are no longer inputs to environment selection. `phase0EnvironmentFor` remains only as a compatibility adapter for legacy callers. The profile implementations are still Haskell-side boundary material in this slice, so INT-004 is not yet complete: later work must make the profile definitions themselves portable and migrate constructor-only Phase-1 negatives.

Exact diagnostic strings and Haskell exception constructors are not conformance authority. The portable class labels in the manifest are semantic labels that implementations map to their own diagnostics.
