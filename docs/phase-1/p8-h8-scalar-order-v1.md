# P8-H8: pure scalar proof scratch preflight (NOT acceptance evidence)

Controlling authority: [#1890](https://github.com/abiggerhammer/phil/issues/1890). This is a disjoint, non-PR scratch rehearsal while P8-H7 [#1862](https://github.com/abiggerhammer/phil/pull/1862) is open. It must **not** be interpreted as an H8 deliverable, protected merge, or native Haskell semantics signoff.

Current scoped proof target: for every C1 well-formed single UTF-8 scalar constructor (1, 2, 3 or 4 octets), the arithmetic value is a legal Unicode scalar. This is stronger than existing fixed witnesses and does not require an axiom about native Text. The candidate numeric encoder and boundary examples are *not yet universal converse proofs*.

Still to derive before H8 PR: universal encoder-validity and value inverse on the entire admitted scalar domain, constructive uniqueness, scalar-vs-byte strict/equal order equivalence, sequence lexicographic order under valid D1 streams, named assumption closure, complete hosted CI and non-PR scratch-path cleanup. H7 must merge through protected checks first. F2 0/1, source-to-native correspondence and T1–T4 remain blocked and untouched.
