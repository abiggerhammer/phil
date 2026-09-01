# Systems runtime claim / cost graph proof v1

This note records the proof boundary for `PHIL-SYS-RUNTIME-GRAPH-001`.

The aggregate sits above three already-landed implementation slices:

- **SYS-015** — many-to-many runtime claim ↔ site binding;
- **SYS-016** — reuse of one runtime primitive/profile without collapsing semantic site, claim, or subject identity;
- **SYS-018** — exact contribution → final-charge cost attribution, with compatible shared physical work charged once.

The normalized Rocq model is `proof/Phil/Core/SystemsRuntimeGraph.v`.

## What the proof establishes

A valid runtime claim/cost graph has:

1. every graph site accepted by the Certified `PHIL-SYS-RUNTIME-001` runtime-site verifier, so it retains exact selected evidence, source revision, and declared runtime cost;
2. an unconstrained many-to-many claim↔site relation: one site may support several distinct claims and one claim may depend on several cooperating sites;
3. an injective **site-owned contribution identity**, so primitive/profile reuse cannot collapse distinct semantic sites into one contribution;
4. a functional **contribution → final charge** relation, so one contribution cannot be counted under two physical/accounting identities;
5. exact class/shape compatibility for contributions that share a final charge; incompatible class or shape cannot be aggregated;
6. claim→charge lineage derived through exact claim→site→contribution→charge edges rather than claims owning physical charge entries directly;
7. reuse of the Certified `PHIL-LLVM-RUNTIME-SYM-001` theorem: revision/evidence/use metadata and claim-set cardinality do not rename or multiply the linker-visible physical primitive identity.

Together these facts capture the assurance-relevant part of “shared mechanism cost is charged once”: several site-owned contributions may point to one final charge identity, while the final charge remains one identity and retains the contributing lineage. The theorem does **not** assert universal numeric performance values.

## Deliberate boundaries

The Rocq theorem does not duplicate concrete Haskell `Text`, `Map`, or `Set` representation, canonical StageContract serialization, or selected-profile cost vocabulary. Those remain implementation/correspondence boundaries.

The dedicated workflow reruns the unchanged production correspondence:

- `src/Phil/Systems/RuntimeClaimBinding.hs` + `test/Phase1RuntimeClaimBindingMain.hs` for SYS-015;
- `src/Phil/Systems/RuntimePrimitiveReuse.hs` + `test/Phase1RuntimePrimitiveReuseMain.hs` for SYS-016;
- `src/Phil/Systems/CostAttribution.hs` + `test/Phase1CostAttributionMain.hs` for SYS-018.

`RuntimeClaimBinding.hs` currently has two pre-existing local bindings named `reverse`; the correspondence-only strict typecheck keeps the existing narrow `-Wno-name-shadowing` exemption rather than weakening production semantics or changing unrelated code.

## Downstream use

Once Certified, this aggregate is the actual upstream cost-graph dependency for `PHIL-MEM-COST-001`. The earlier `PHIL-SYS-COST-001` dependency label in the memory row was stale and had no ledger or repository definition; it was reconciled to this obligation on 2026-09-01.
