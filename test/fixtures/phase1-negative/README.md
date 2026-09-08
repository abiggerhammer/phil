# Phase 1 portable negative corpus

This directory begins the INT-004 migration from implementation-private negative tests to portable conformance fixtures.

`manifest.tsv` is normative for the migrated frozen Phase-0 semantic negatives. Each row gives a stable fixture identity, portable `.phil` input path, implementation-independent rejection class label, earliest competent rejection layer, explicit environment profile name, and governing Matrix authority.

The current first slice intentionally keeps `Phil.Surface.Phase0.phase0EnvironmentFor` only as a temporary Haskell adapter for the named environment profiles and checks parity with the frozen legacy classification table. The manifest, not the filename table, owns the expected rejection class for the INT-004 replay. A subsequent slice will materialize the environment profiles portably and remove filename dispatch from the replay path.

Exact diagnostic strings and Haskell exception constructors are not conformance authority. The portable class labels in the manifest are semantic labels that implementations map to their own diagnostics.
