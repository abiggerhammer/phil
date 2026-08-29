# PHIL-DATA-SUBJECT-001 — stable subject update proof

This proof certifies the Phase 1 DATA-012 semantic boundary for evidence bound to stable subjects across consume-and-reconstruct updates.

## Certified semantic core

`proof/Phil/Core/DataSubject.v` proves:

- an accepted update requires explicit predecessor consumption and replacement construction;
- predecessor and replacement are stable semantic subjects of the same stable-id kind;
- subject-bound evidence must actually mention its distinguished subject and must initially be bound to the exact predecessor subject;
- the checked result preserves the exact evidence reference/template while targeting the exact replacement subject;
- a genuine subject change cannot be accepted without an explicit transport;
- matching stable-id kind alone does not authorize evidence retargeting;
- matching representation/pointer/handle/SSA metadata alone does not authorize evidence retargeting;
- an unchanged semantic subject rejects a spurious transport witness;
- every accepted changed-subject transport has an accepted disposition, nonempty relation revision, exact evidence reference, exact predecessor/replacement identities, and exact source/target proposition instances; and
- representation changes on one unchanged stable semantic subject are nonsemantic for subject identity.

The transport kind may be either copy or succession. This theorem does not infer the truth of either relation from its label; relation truth is explicit assurance/discharge input.

## Composition

`PHIL-DATA-ELIM-001` owns the concrete restricted-value consumption/construction discipline. DATA-012 consumes those lifecycle facts as explicit premises rather than re-proving aggregate elimination.

The accepted copy/succession relation is an assurance boundary: DATA-012 proves that retargeting is impossible without a witness bound to the exact evidence, subjects, revision, and propositions, but it does not prove the external truth of that witness.

## Correspondence gate

The dedicated `Phase 1 Data Subject Proofs` workflow:

- compiles the proof under Rocq 9.2.0;
- records exact source and `.vo` SHA-256 identities;
- typechecks unchanged `src/Phil/Core/DataSubjectTransport.hs` and `test/Phase1DataSubjectTransportMain.hs` under `-Wall -Werror`; and
- reruns the unchanged DATA-012 **19-case** conformance corpus from #271.

That corpus covers same-subject preservation, exact succession acceptance, distinct-subject rejection without transport, stable-kind and representation non-implication, exact evidence/source/target binding, rejected/scope-less relations, lifecycle facts, stable identity constraints, subject-bound template requirements, and spurious same-subject transport rejection.

## Residual assumptions / non-claims

This is semantic certification, not implementation refinement. The following remain explicit boundaries:

- Rocq kernel/toolchain correctness;
- concrete `RefTerm`, `Proposition`, `Text`, and representation-token correspondence;
- source-to-Core stable-subject elaboration;
- concrete proposition substitution/normalization correspondence;
- truth/competence of accepted copy or succession relations;
- same-subject post-mutation evidence validity;
- pointer/SSA/object identity correspondence;
- boundary zero-copy subject transfer and Systems subject correspondence;
- diagnostics and Haskell implementation equivalence.
