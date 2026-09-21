# PHIL-AUD-DIGEST-SUBJECT-001 — proof-correspondence remediation staging

Astra's validator-subject audit found that the original Surface `DigestMatches`
producer checked source readability but constructed evidence for one fixed
witness-shaped subject pair. The implementation repair now validates the
actual ordered subjects and preserves a stable byte-owner identity.

This tranche supplies the missing proof-facing correspondence boundary without
changing production Haskell.

## Normalized proof claim

`proof/Phil/Surface/DigestSubjectCorrespondence.v` models the exact ordered
Surface admission sequence for the repaired DigestMatches route:

1. no explicit validation context;
2. exactly two ordered subjects;
3. the first subject is a name;
4. that subject has Begin semantics;
5. the second subject is a borrowed view;
6. that view carries a stable owner identity; and
7. the second subject has the exact SharedBytes validator type.

The decision is polymorphic in the concrete Begin-subject and stable-owner
representations. On acceptance it **returns those exact values unchanged**.

That gives the proof the anti-substitution property the implementation repair
needs:

- alpha-renaming the borrowed view spelling cannot change the evidence owner,
  because view spelling is not an input to the semantic result;
- a legal ownership-preserving move can retain the same stable owner;
- two distinct stable owners remain distinct through accepted decisions; and
- no rejected schema case can manufacture an accepted subject pair.

The rejection constructors also preserve the current native diagnostic order.

## Extracted staging kernel

`DigestSubjectCorrespondenceExtraction.v` extracts
`SurfaceDigestSubjectKernel.hs`.

The direct controls use ordinary Haskell values for the polymorphic carried
subjects and verify exact value preservation, owner non-collapse, and all seven
ordered rejection cases.

This staging kernel does not yet alter `evalValidate`.

## Production-binding successor

The next tranche will bind the repaired `evalValidate` DigestMatches route to
the exact extracted kernel:

- native source/type/shape diagnostics remain first;
- the actual checked `Name` and actual stable-owner `RefTerm` are passed into
  the extracted decision;
- successful kernel output must return those same concrete values;
- the emitted `Atom "DigestMatches" [RefVar beginName, stableOwner]` will be
  constructed from the kernel-returned subjects; and
- any native-success/kernel-reject or subject-substitution disagreement fails
  closed.

That successor is the production correspondence evidence required to close the
proof-status portion of `PHIL-AUD-DIGEST-SUBJECT-001`.

## Residual boundaries

This proof does not prove digest cryptography, generic validator semantics,
Haskell Text/RefTerm representation, parser correctness, or downstream
Systems/LLVM realization. Existing certified Systems/LLVM digest proofs remain
separate downstream authorities.
