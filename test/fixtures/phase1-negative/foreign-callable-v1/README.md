# Portable CALL-015 negative corpus v1

This corpus carries implementation-independent inputs for the competent foreign-callable qualification boundary.

- `manifest.tsv` owns stable fixture identity, expected portable rejection, competent layer, and exact Matrix/Certified authority.
- `surfaces-v1.tsv`, `authority-requirements-v1.tsv`, `effect-bounds-v1.tsv`, and `failures-v1.tsv` describe expected, observed, and (when present) qualified callable semantic surfaces.
- `artifacts-v1.tsv` records exact foreign artifact identity, qualification presence, and qualification target identity.
- `evidence-v1.tsv` records the five explicit qualification evidence dimensions without Haskell constructor names.
- `authority-registry-v1.tsv` resolves every used Matrix/Certified authority and checked-in proof source exactly.

The replay adapter may translate this portable vocabulary into the current Haskell checker API, but Haskell constructors, diagnostic strings, and fixture-ID dispatch are not conformance authority. Qualification/reference checks must reach the recorded CALL-015 rejection; a later CALL-012 refinement rejection must not be satisfied by an earlier missing-evidence, artifact, or surface failure.
