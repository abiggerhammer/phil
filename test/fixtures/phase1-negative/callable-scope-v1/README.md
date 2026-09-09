# Portable callable-scope negative corpus v1

This corpus carries CALL-010 and CALL-014 negative conformance at the bounded callable-scope competence boundary without Haskell-private fixture construction.

`manifest.tsv` gives stable fixture identity, expected portable rejection class, competent layer, and exact Matrix/Certified authority. `scope-captures-v1.tsv` describes closure extent and scope-relevant captures. `recursion-nodes-v1.tsv` and `recursion-references-v1.tsv` describe recursive closure-environment graphs. `authority-registry-v1.tsv` resolves every authority reference.

The replay adapter may translate this portable vocabulary into the current Haskell checker API, but Haskell constructors, exception names, diagnostics, and fixture IDs are not conformance authority. For every fixture, rejection must occur at the recorded callable-scope layer rather than at an earlier unrelated setup failure.
