# Steve systems-pressure-test material

`lowering-contract.md` is the current Steve 0 mapping from the semantic/assurance witness into Phil's ADR-007/010/011 Systems IR. It remains the design-level description of the intended `StevePut`/`SteveGet` control flow, ownership, runtime checks, cost model, and eventual executable-promotion criteria.

`generalization-handoff.md` is the implementation/proof handoff extracted from that pressure test. It turns the four representation gaps into concrete generic Haskell and Rocq targets:

- first-class assumption authority on stage facts, including mixed transferred-plus-assumption facts;
- multiple exact assurance claims on one physical runtime site without duplicating the physical cost;
- checked provider-capability possession and call authority, so absence of replace/delete authority is structural rather than inferred from unused calls;
- binding persistent assurance subjects to stable owner/storage identity while borrowed views remain observation mechanisms.

The material here is intentionally design-first rather than an executable `SystemsArtifact`. The current upload-derived Systems implementation and proof corpus should be generalized, not copied around with Steve-specific exceptions.

The branch is synchronized through main PR #36. That includes the Systems ownership/runtime proofs (#31), LLVM translation-validation proofs (#33), runnable compiler and typed scalar path (#32/#34), concrete Phase 0 LLVM translation certification (#35), and the first real checked Surface -> Systems scalar SSA/dataflow lowering (#36). These strengthen the boundary Steve is pressure-testing: the four findings above now cut across already-mechanized Systems and LLVM contracts, so the handoff explicitly calls out the corresponding proof generalizations and requires the existing Phase 0 artifacts to remain singleton cases.

PR #36 was deliberately developed independently of Steve and has now satisfied the first sequencing item in `generalization-handoff.md`: establish a generic checked Surface -> Systems lowering path before attempting Steve-specific resource/provider lowering. The next work requested by the handoff begins at the generic Systems representation itself, not in the runnable scalar compiler fragment.

Steve rejected fixture 02 is also promoted from parser-only status to a branch-local semantic test suite: `test/SteveSurfaceSemanticMain.hs` supplies only the generic opaque `DigestMatches` static declaration and requires the existing checker to reject generic `prove` with exactly `OpaqueProof`. This gives Steve its first checker-level semantic pressure test without adding Steve-specific Core logic.

Once the four Systems generalizations in `generalization-handoff.md` are available, the promotion target here is an honest executable Steve Systems artifact plus the adversarial mutations listed in the handoff and `lowering-contract.md`.
