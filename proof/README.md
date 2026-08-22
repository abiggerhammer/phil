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

The checked corpus includes session duality, exact binding insertion and linear consumption, session progression resources, label selection, process sequencing, recognition provenance/gating, branch convergence, terminal-state resource completeness, assurance disposition, linear-certificate soundness, finite session-head exposure, and deterministic focusing competence. See the stable obligation IDs in the individual proof files and the Drive logic ledger for the authoritative claim registry.

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

## Focusing competence slice

`proof/Phil/Core/Focusing.v` formalizes the deterministic pre-solver competence boundary introduced by `Phil.Core.Focusing`. The proof is intentionally about what focusing is authorized to construct or classify; it does not turn the later decision procedure or an explicit runtime/export mechanism into an implicit source of truth.

### PHIL-FOCUS-COERCE-001 — one-way canonical coercion

The proof-side elaborator has exactly one implicit cross-sort success case: a term already known to have `UInt[w]` sort may be elaborated in a Nat context only as explicit `toNat(term)`, with the insertion recorded. Already matching sorts are identity elaborations. A Nat term presented to a `UInt[w]` context rejects. Every successful elaboration has the requested result sort.

Concrete Haskell sort inference is outside this theorem: the proof takes the inferred source sort as the competence-boundary input and proves what focusing may do with it.

### PHIL-FOCUS-CLAIM-001 — declared claim expansion only

A claim focus step first requires an actual declaration and successfully elaborated arguments. Opaque declarations preserve the same claim identity and only the elaborated arguments. A well-scoped transparent declaration expands to exactly its declared instantiated body. A transparent claim already present on the expansion stack rejects, as does a declaration already known to be ill-scoped. Thus the focusing layer has no successful path that invents an unknown claim body or treats recursive transparent expansion as authority.

The proof represents a transparent declaration body as its capture-avoiding parameter-instantiation function. Correspondence with the concrete substitution implementation and Map lookup remains explicit rather than assumed as a logical theorem.

### PHIL-FOCUS-PREREQ-001 — side conditions survive assembly

Side-condition focus plans contribute both their own prerequisites and their focused goals to the parent prerequisite set. Canonical-key deduplication may merge duplicates but cannot remove the final representative of any side goal or nested prerequisite. This is the structural reason a partial-operation side condition cannot disappear merely because normalization later simplifies the parent proposition.

The side-condition extractor and proposition normalizer are deterministic implementation inputs to this slice; the theorem covers focus-plan assembly and deduplication rather than re-proving arithmetic normalization.

### PHIL-FOCUS-MECH-001 — closed mechanism classification

Mechanism selection is modeled with the same precedence as the implementation. Canonical Truth is definitionally discharged. For every non-Truth goal, matching evidence wins before later boundaries. Without matching evidence, Falsehood is statically rejected, an unresolved opaque goal requires an explicit mechanism, and every other unresolved transparent goal stops at the decision-procedure boundary. There is no additional constructor that can silently authorize a goal.

Evidence search itself is abstracted to the result of canonical evidence matching; the theorem proves the authority-bearing classification once that deterministic search result is known.

### PHIL-FOCUS-BRANCH-001 — exact branch coverage

Successful branch checking is the conjunction of duplicate-free declared labels, duplicate-free handler labels, and extensional equality of the two label sets. Any duplicate, missing handler, or extra handler excludes success. The proof models label sets extensionally; the implementation's deterministic ordering of missing/extra diagnostic lists remains covered by the Haskell conformance suite.

## Surface elaboration competence slice

`proof/Phil/Surface/Elaboration.v` models the proof-relevant competence boundary of `Phil.Surface.Elaborate`. Parsed surface nodes are inputs: this file does not pretend to verify Megaparsec. The proof instead constrains what the elaborator may construct once a surface fragment has been accepted syntactically.

### PHIL-SURFACE-ELAB-001 — canonical supported elaboration

Supported refinement expressions map structurally to the designated Core constructors: variables, literals, Boolean terms, projections carrying the exact declared projection sort, `len`, explicit `toNat`, Nat addition/subtraction, and literal scaling. Greater-than/greater-equal propositions lower to the corresponding reversed Core less-than/less-equal form. Proof propositions delegate exactly once to the supplied canonicalization boundary. `Bytes[...]` delegates its already-elaborated raw index exactly once to the supplied expected-Nat boundary. In the implementation both supplied boundaries are `Phil.Core.Focusing`, whose authority properties are independently discharged by the `PHIL-FOCUS-*` slice.

The theorem models opaque named-type arguments by a canonical structural key rather than reproducing the concrete Text rendering. Correspondence between those keys and `renderNamedType` string serialization remains an implementation/tested representation obligation; no injectivity claim about arbitrary Text serialization is smuggled into this proof.

### PHIL-SURFACE-FAIL-001 — no proof-relevant guessing

The proof model has no successful path for an unknown projection sort, symbolic-by-symbolic multiplication outside the Phase 0 refinement fragment, a non-name validation context/subject identity, an unsupported opaque type argument, or an integer literal with no expected UInt width. These are competence-boundary failures rather than defaults. Source-span precision and the exact Haskell error constructor are implementation-level tested properties.
