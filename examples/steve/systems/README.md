# Steve systems-pressure-test material

`lowering-contract.md` is the current Steve 0 mapping from the semantic/assurance witness into Phil's ADR-007/010/011 Systems IR. It remains the design-level description of the intended `StevePut`/`SteveGet` control flow, ownership, runtime checks, cost model, and eventual executable-promotion criteria.

`generalization-handoff.md` is the implementation/proof handoff extracted from that pressure test. It turns the four representation gaps into concrete generic Haskell and Rocq targets:

- first-class assumption authority on stage facts, including mixed transferred-plus-assumption facts;
- multiple exact assurance claims on one physical runtime site without duplicating the physical cost;
- checked provider-capability possession and call authority, so absence of replace/delete authority is structural rather than inferred from unused calls;
- binding persistent assurance subjects to stable owner/storage identity while borrowed views remain observation mechanisms.

The material here is intentionally design-first rather than an executable `SystemsArtifact`. The current upload-derived Systems implementation and proof corpus should be generalized, not copied around with Steve-specific exceptions.

The branch now includes the merged Systems ownership/runtime proof tranche (#31), LLVM translation-validation proof tranche (#33), runnable compiler and typed scalar path (#32/#34), and the concrete Phase 0 LLVM translation certification (#35). Those strengthen the boundary Steve is pressure-testing: the four findings above now cut across already-mechanized Systems and LLVM contracts, so the handoff explicitly calls out the corresponding proof generalizations and the requirement that the existing Phase 0 artifacts remain singleton cases.

Steve rejected fixture 02 is also promoted from parser-only status to a branch-local semantic check: `test/SteveSurfaceSemanticMain.hs` supplies only the generic opaque `DigestMatches` static declaration and requires the existing checker to reject generic `prove` with exactly `OpaqueProof`. This gives Steve its first checker-level semantic pressure test without adding Steve-specific Core logic.

PR #36 is deliberately treated as independent work: it is establishing the first real checked Surface -> Systems scalar SSA/dataflow lowering. Do not fold Steve-specific resource/provider lowering into that tranche. Once the four generalizations in `generalization-handoff.md` are available, the promotion target here is an honest executable Steve Systems artifact plus the adversarial mutations listed in the handoff and `lowering-contract.md`.
