# Portable CALL-012 negative corpus v1

This directory records six implementation-independent negative fixtures for the Phase-1 callable semantic-refinement boundary.

`manifest.tsv` owns stable fixture identity, intended rejection class, competent layer, and exact Matrix/Certified authority. `surfaces-v1.tsv` records the expected and actual callable machine shape, interface revision, and callee transition. Authority requirements, public effect bounds, and modeled non-success behavior are normalized into separate repeated-row tables.

The portable data does not name Haskell constructors, exception text, implementation symbols, or fixture-specific scenarios. The replay adapter translates this vocabulary into the production `checkCallableRefinement` boundary and requires the recorded rejection class and diagnostic payload. Corruption checks also exercise the checker’s precedence order so an earlier unrelated mismatch cannot satisfy a later expected rejection.
