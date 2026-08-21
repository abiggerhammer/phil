# Phil: Initial Trusted Computing Base Statement

## Goal

Keep the set of components whose defects can invalidate Phil’s assurance claims as small, explicit, and replaceable as practical. Phil's semantic identity should reside in executable architecture, checked obligations, and observable behavior rather than in any one prototype or production implementation.

## Assurance identity

For the first vertical slice, the stable object being assured is the combination of:

- architectural declarations;
- their Phil Core elaboration;
- generated and discharged obligations;
- the reference observable trace semantics.

A Haskell prototype, a Rust rewrite, or another executable realization is not trusted merely because it descends from an earlier implementation. Each realization must independently satisfy this assurance identity.

## Trusted in the first vertical slice

1. **Source parser**
   - Must parse Phil without ambiguity.
   - Must preserve source locations used in diagnostics and evidence records.

2. **Elaborator**
   - Resolves names and static declarations in `Σ`, inserts canonical structural operations, projects local session types, generates stable obligation identities, and elaborates surface syntax into explicit Phil Core.
   - Must not silently weaken obligations, choose computational protocol branches, insert undeclared runtime validators, or turn unresolved propositions into assumptions.
   - Focusing/canonicalization must preserve program-visible choices while collapsing deterministic elaboration choices as specified by ADR-001.

3. **Phil Core checker**
   - Checks the accepted provider/bidirectional Core judgments, unrestricted/affine/linear usage, scoped shared-loan lifetimes, session transitions, guarded recursion, definitional equality, explicit propositional transport, and explicit evidence.
   - Implements or invokes the small ADR-006 refinement assurance boundary: typed refinement terms, transparent claim expansion, definitional normalization, evidence-to-proposition/context/subject matching, and certificate verification.
   - Must not allow a shared loan to outlive its owner or permit ownership-consuming operations while that loan is live.
   - External SMT/theorem-prover answers are not trusted unless converted to evidence checked here or explicitly classified as trusted in the assurance ledger.
   - Opaque claims cannot be introduced by generic proof search; only declared evidence producers may establish them.
   - Definitional equality must not depend on arbitrary solver proof search; nontrivial equalities require explicit checked evidence/transport.
   - This is the central executable trust anchor.

4. **Assurance-ledger / manifest verifier**
   - Checks ADR-010 obligation-revision identity and statement digests, evidence/assumption/dependency referential integrity, acyclic justification graphs, acceptance-rule satisfaction, validity scopes, architecture permission for assumptions/exports, runtime-enforcement mappings, and assurance/lowering-ledger cross-references.
   - Rejects a requested certified scope containing unresolved obligations, stale/inapplicable evidence, dangling dependencies, or unapproved assumption boundaries.
   - Does not need to build or prettify the ledger; a separate ledger builder/report generator may be untrusted if the verifier checks its output.

5. **Reference operational semantics / interpreter**
   - Defines the observable trace behavior used for differential checking.

6. **Boundary codec construction rules**
   - Recognizers must ensure that successful recognition establishes complete membership in the declared grammar and preserves byte provenance.
   - Generated/trusted encoders for `Frame[G]` must emit complete frames belonging to `G` for every accepted `ValueOf[G]` input and preserve the declared semantic value relation.
   - Split receive adapters must not expose a semantic successor endpoint before the matching boundary evidence commits the `PendingRecv[...]` resource.
   - Raw frame inspection exposed from a pending receive must remain a non-owning view whose lifetime cannot exceed the pending owner.

7. **Checked-lowering / stage-contract boundary**
   - Initially trusted for cross-stage preservation not yet covered by translation validation or proof.
   - Implements ADR-007's fact-transfer rule across Core, protocol/boundary, systems, and backend/target competence layers.
   - Each physical IR has a local verifier for its own well-formedness; local well-formedness is not treated as proof of source-to-target semantic preservation.
   - Must preserve still-live semantic facts when proof terms/typestate/evidence representations are erased.
   - Must preserve the accepted observable trace relation and ADR-005 failure/resource behavior across lowering.
   - Any lowering-specific preservation fact that is not definitionally evident must become an explicit ADR-010 obligation/evidence edge rather than an undocumented compiler assumption.
   - Over time, lowering passes should become untrusted producers whose source/target relation is checked by translation validators or proof-producing transformations.

8. **Systems/backend representation and cost lowering**
   - Implements ADR-011 representation roles and compilation-profile rules.
   - Decides allocation, copying, layout, control-flow typestate representation, runtime-check residue, target-facing ownership facts, and concrete representation of shared loans/views.
   - Must not remove an ADR-010 runtime-bound enforcement mechanism merely because the manifest is certified.
   - Must not erase a proof/check before every downstream consumer has received the corresponding invariant or derived obligation.
   - Must classify retained material cost as semantic-required, runtime-assurance-required, target-required, defensive-profile, or conservative-lowering residue.
   - Must not extend a loan beyond its owner or invent stronger aliasing, range, alignment, provenance, or definedness claims than accepted evidence supports.

9. **LLVM emission boundary**
   - Initially trusted for the backend/target -> pre-optimization LLVM stage contract until covered by translation validation/proof.
   - Must preserve every reachable ADR-010 runtime-bound enforcement mechanism and ADR-005 cleanup/failure edge.
   - May emit LLVM optimizer-strengthening flags, attributes, assumptions, or semantic metadata only when artifact-scoped evidence establishes their exact LLVM preconditions.
   - Must not infer backend contracts mechanically from Phil vocabulary: linear ownership is not automatically LLVM `noalias`; a logical bound is not automatically `range`/`inbounds`; untrusted pointers are not automatically `nonnull`/`noundef`.
   - Must enforce ADR-008's no-accidental-poison/undefined-behavior discipline on Phil-defined executions and must not replace modeled runtime failure with LLVM UB.
   - Records LLVM language/tool version, target triple/data layout, runtime ABI identity, artifact digest, emitted strengthening facts/evidence IDs, and stage-contract cross-links.
   - Local LLVM verifier success establishes LLVM well-formedness only; it is not treated as cross-stage preservation evidence.

10. **Runtime primitives**
   - Ordered transport, pending-receive lifecycle, scoped read-only frame/payload views, exact-length receive, buffer ownership, checked arithmetic with proof-relevant success postconditions, declared runtime validators, cancellation, and cleanup.
   - A runtime validator may produce evidence only for the exact claim/context/subject named by its contract; failure must follow ADR-005 resource semantics.
   - The runtime API must be narrow and contractually specified.

## Not trusted for source-level correctness

- software-writing agents;
- source generators;
- assurance-ledger builders/report generators whose output is checked by the ledger verifier;
- formatters;
- IDEs;
- theorem provers used only to propose proof terms;
- SMT solvers when their results are certificate-checked;
- LLVM optimization passes and code generation;
- system assembler/linker/native toolchain unless a particular assurance manifest explicitly includes them as assumptions or stronger artifact-specific evidence;
- foreign code outside generated adapters.

## Independent-checker qualification

ADR-001 permits a checker to implement the provider-oriented rules directly or to implement the accepted bidirectional residual-resource presentation.

That engineering choice is not itself trusted as a semantic difference. A conforming checker must agree on:

- accepted/rejected Phase 0 programs;
- resource consumption/residue;
- session-state progression;
- definitional equality versus explicit transport;
- generated obligation identities/propositions;
- evidence competence/matching rules;
- canonical Core meaning relevant to observable traces.

Differential checking between independently implemented Core checkers is therefore a useful TCB-reduction strategy.

## Important qualification

LLVM and the native toolchain can still miscompile the executable. They are outside the logical kernel but remain part of the deployment supply chain. Initial assurance should therefore distinguish:

- source-level semantic assurance;
- correctness of lowering;
- correctness of native compilation;
- correctness of execution environment;
- empirical performance of the selected representation and target backend.

## Target reduction over time

1. Make the Phil Core checker small and independently specified.
2. Differentially compare at least two checker implementations or validate elaboration output against an independently implemented Core checker.
3. Translation-validate the backend/target -> pre-optimization LLVM emission boundary first, then other important lowering/optimization passes.
4. Replace solver trust with checkable certificates where possible.
5. Differentially test optimized native traces against the reference interpreter.

## Performance assurance boundary

Phil's semantic assurance does not by itself prove a wall-clock performance claim. The checker, assurance manifest, and lowering/cost ledger can establish that specified proof artifacts and redundant checks were erased with valid justification, and can attribute every retained semantic/assurance/target/profile/conservative mechanism. Throughput, latency, allocation behavior, code size, and backend quality remain empirical properties measured for a particular target and deployment.

The guiding rule is:

> **Phil makes the cost of assurance explicit and erases assurance machinery that has completed its work.**

> **Proof should cost at compile time; uncertainty should cost at runtime.**
