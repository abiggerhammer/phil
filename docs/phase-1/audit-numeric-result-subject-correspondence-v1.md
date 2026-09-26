# Phase 1 audit: returned numeric result to dependent subject

This defensive proof-correspondence slice addresses the still-open
`D-NUM-RESULT-SUBJECT-01` boundary after adoption of the supplied/trusted
numeric-environment contract.

The numeric handoff distinguishes exact mathematical conversion from semantic
subject identity. A conversion can preserve UInt width and magnitude exactly
while still referring to a different same-typed subject. That is not sufficient
authority for a dependent refinement or indexed consumer.

`NumericResultSubjectCorrespondence.v` therefore makes the bounded relation
explicit:

- the result is an actual returned numeric result;
- the consuming operation identifies that same returned result;
- exact width and mathematical magnitude are preserved;
- the authentic result subject and the consumer subject are the same;
- conversion is exact; and
- the dependent consumer actually accepts that subject.

The negative witness preserves the exact 32-bit value 7 and reports an exact
conversion, but attaches it to subject 71 rather than the returned result's
subject 70. The weaker same-typed/value relation succeeds while the complete
subject correspondence fails. The positive witness preserves result, width,
magnitude, subject, and final consumer together.

## Native correspondence boundary

This theorem does not manufacture the native mapping. Production must reflect
the actual returned numeric value and the supported next consumer into these
fields. In particular, `NumericConversionExact`, equal width, equal magnitude,
source spelling, or an unrelated same-typed binding cannot establish subject
identity by themselves.

Closed numeric constants may remain reusable under their existing contract;
this slice concerns subject-bearing dependent consumers. Resource ownership,
evidence authority, and numeric interpretation remain separate concerns.

This PR is proof/docs/workflow-only. It does not add a generalized Phase 2
registry, alter numeric semantics, restore consumed owners, change native
lowering, or expand the Phase 1 trusted-computing-base boundary. LLVM remains
trusted in Phase 1.
