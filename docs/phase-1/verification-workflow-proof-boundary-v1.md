# Verification workflow proof boundary v1

This note records the normative certification boundary for `PHIL-VERIFY-WORKFLOW-001`.

## What this proof owns

The proof certifies the orchestration contract implemented cumulatively by VER-001 through VER-012:

- intrinsic rejection is terminal and cannot be converted into a residual obligation by selecting a more permissive assurance policy;
- only intrinsic acceptance reaches obligation closure, retaining the exact selected policy identity;
- the residual obligation graph is finite, exact, internally referenced, certification-scope closed, and acyclic;
- source revision, declaration identities, architecture instance identities, architecture realization identities, exact obligation graph, assurance-policy revision, and accepted evidence references remain explicit coordinates of the independent `VerificationBundle`;
- evidence enters the bundle only when the already-competent evidence layer reports it accepted, its content digest matches, its target obligation revision is present, and its stable evidence identity is conflict-free;
- rejected, stale, wrong-target, or conflicting evidence cannot become bundle authority;
- semantic sets are insensitive to container/list order and exact duplicate presentation; and
- changing an identity-bearing source, graph, policy, declaration, instance, realization, or accepted-evidence coordinate changes the verification target rather than silently reusing unrelated authority.

The executable correspondence layer reflects the finite admission facts used by production after predecessor competence has run and proves that the executable decision accepts iff the certified semantic workflow admission relation holds.

## Imported competence

This certification does **not** re-prove the parser, surface checker, semantic obligation generator, proof checker, generic checker, architecture checker, provider checker, or other competent semantic layers. Their accepted/rejected facts are inputs to this orchestration boundary.

`PHIL-VERIFY-REUSE-001` separately certifies reuse of already accepted evidence across later semantic contexts. `PHIL-ASSURE-VALIDITY-001` owns validity-scope applicability. `PHIL-ASSURE-GENERIC-001` owns reusable conditional generic-body assurance. This workflow proof composes those authorities rather than replacing them.

## Representation and implementation boundary

Concrete `Text`, `Digest`, `RevisionId`, `Data.Map`, `Data.Set`, canonical text rendering, SHA-256/digest construction, derived Haskell equality/ordering, and detailed diagnostic payload ordering remain representation/runtime boundaries.

The proof treats source/declaration/architecture/revision/evidence identities as normalized atoms. It proves the orchestration relation over those atoms; it does not claim Rocq verifies their concrete serialization or hash collision resistance.

The exact Haskell `VerificationBundle` revision remains the concrete content-bound serialization of the certified coordinates. The correspondence gate reruns the unchanged VER-001 intrinsic-invalidity corpus, VER-002 canonical-obligation-graph corpus, VER-012 independent-target corpus, and the already-certified VER-006 reuse corpus.

## Non-claims

This proof does not certify every later obligation disposition, proof producer, artifact realization, backend, or runtime. In particular:

- producer/checker separation remains `PHIL-VERIFY-PRODUCER-001`;
- RuntimeBound / AssumptionDependent / Exported policy closure remains `PHIL-VERIFY-POLICY-001`;
- source assurance to emitted-artifact certification remains `PHIL-VERIFY-ARTIFACT-001`.

Those successors may import this certified workflow boundary and focus on their own additional semantics.
