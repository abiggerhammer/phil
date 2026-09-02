# Generic requirement category proof v1

`PHIL-GEN-CATEGORY-001` certifies the bounded Phase 1 `GEN-014` rule implemented by `Phil.Core.Generic.RequirementCategory`.

The proof fixes one semantic handoff discipline for every public generic requirement. A requirement keeps its exact stable key, semantic category, and semantic payload. Its category deterministically selects one competent checker. A proposed handoff may neither substitute another category nor route the requirement through a checker competent for another category. It also may not convert the requirement directly into an assumption; any later assumption disposition belongs to an explicit enclosing assurance-policy boundary rather than generic-interface checking.

The normalized interface theorem also requires exact requirement/handoff/result domains: every public requirement has one checked handoff and no handoff may appear for a requirement absent from the interface. Successful handoff preserves the exact key, category, semantic payload, and category-selected competence.

The theorem intentionally does not duplicate the truth conditions of structural, proposition, provider, callable, boundary, architecture, effects, authority, boundary-representation, representation, placement, cost, or environment requirements. Those remain owned by their competent semantic checkers. Concrete Haskell `Text`/`SemanticForm` representation, `Map`/`Set` normalization and duplicate detection, deterministic diagnostic ordering, and source elaboration into the public requirement/handoff records remain explicit correspondence boundaries.

The dedicated workflow compiles the Rocq theorem with Rocq 9.2.0, strictly typechecks the unchanged production checker and `GEN-014` corpus with `-Wall -Werror`, and reruns all six focused conformance cases.
