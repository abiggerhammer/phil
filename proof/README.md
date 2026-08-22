# Phil proof corpus

This directory contains the checked mechanized evidence for Phil assurance obligations.

The human-facing logic ledger lives in Drive. The repository is authoritative for whether an obligation is actually discharged at a particular commit.

## Conventions

- Rocq is the canonical prover for normative Phil metatheory and refinement proofs.
- Every theorem intended to discharge a ledger obligation names the stable obligation ID in a nearby comment.
- `Admitted`, undeclared axioms, and opaque trust shortcuts do **not** discharge an obligation. If one is temporarily necessary, the corresponding assumption must remain explicit in the ledger.
- Small proof models may abstract implementation details that are irrelevant to the theorem, but those abstractions must be stated explicitly and tightened before stronger claims depend on them.
- Proofs should follow the implementation slices closely enough that semantic drift is visible in review.

## Existing discharged slices

The checked corpus includes session duality, exact binding insertion and linear consumption, session progression resources, label selection, process sequencing, recognition provenance/gating, branch convergence, and terminal-state resource completeness. See the stable obligation IDs in the individual proof files and the Drive logic ledger for the authoritative claim registry.

## Assurance-disposition slice

`proof/Phil/Core/Discharge.v` formalizes the checker-to-ledger authority boundary introduced by `Phil.Core.Discharge`.

### PHIL-DISCH-CERT-001 — producer/checker separation

The certificate producer is represented separately from the checker. A producer result becomes a static certificate discharge only when the checker accepts that exact certificate for the exact canonical proposition. No proposal falls through to an explicit mechanism; a rejected produced certificate is an error rather than proof.

### PHIL-DISCH-BOUNDARY-001 — exact disposition authority

Successful resolution has only the implemented explicit forms: definition, matching evidence, checked certificate, exact runtime binding, or exact export binding. Runtime and export bindings carry exact obligation identity, canonical proposition, and required point. There is deliberately no local `Assumed` constructor.

The proof treats proposition canonicalization as the equality boundary already established by the checker. Full ADR-010 artifact identity and closed-manifest validation remain later assurance obligations.

### PHIL-DISCH-PREREQ-001 — export is not truth

An exported prerequisite produces no local assumption. If any prerequisite is exported, the parent is not locally resolvable in this model and must itself take an explicit boundary disposition. This is the mechanized form of the policy: transferring an obligation is not satisfying it.

## Linear-certificate semantic slice

### PHIL-DECISION-LINEAR-001 — linear combination soundness

`proof/Phil/Core/DecisionSound.v` proves the mathematical kernel beneath `phil-core-linear-certificate-v1`. Equality bases denote zero and may be combined with arbitrary rational coefficients. Inequality bases denote nonnegative quantities and may contribute to inequality goals only with nonnegative coefficients; inequality slack is nonnegative, while equality slack is exactly zero. Under those checker restrictions, an accepted affine combination semantically satisfies its target relation.

The same checked judgment carries partial-operation prerequisites explicitly, so certificate acceptance cannot erase Nat-subtraction or similar definedness requirements. The correspondence from Haskell `RefTerm` normalization/sort checking and the concrete affine map representation to the proof-side rational denotation remains explicit rather than being smuggled into the theorem.

## Session recursion slice

### PHIL-SESSION-REC-001 — finite head exposure

`proof/Phil/Core/SessionRec.v` gives a structurally terminating Rocq mirror of `exposeSessionHead`. It proves that session substitution cannot invent recursion binder names at the session-structure level, each fresh unfolding strictly enlarges the seen set, and every unfolding trace is bounded by the number of distinct recursion names in the initial session. The derived fuel therefore cannot be exhausted. Every result is a non-recursive head, an unguarded repeated recursion result, or an unbound session variable.

Message types remain opaque in this slice because head exposure never inspects them; substitution inside endpoint/message types cannot create a new top-level head during the operation. This theorem proves the implemented finite seen-set behavior, not a stronger global guarded-recursion property.
