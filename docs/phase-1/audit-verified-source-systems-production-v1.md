# #1584 P2: source-owned production from actual checked source

This first inventory-linked implementation/proof slice (budget 1/3) introduces
a constructor-private `VerifiedSourceSystemsProduction`. Its only public
producer, `produceVerifiedSourceSystems`, takes an ordinary portable source
bundle and runs the existing source parser/validator, persisted occurrence
lineage resolution, architecture instantiation, exact Core correspondence
policy admission, and actual `lowerGenericSystems` via `lowerSourceSystems`.

The private result retains the verified source/Core admission with exact
producing occurrence K/I and the **complete** emitted `Phase1StageBundle`.
The new producer does **not** accept a caller-built
`CheckedSourceArchitecture`, whose public record constructor would
otherwise allow a misleading minting path. The source environments, root
and lineage policy, Core program and checker remain the existing Phase 1
accepted-domain inputs; no cryptographic provenance or new trusted
compiler assumption is invented.

Executable Upload and Steve ordinary-source tests must recheck full
source admission, exact real persisted occurrence keys, native stage instance
revision and *whole-stage equality* against the existing successful producer.
A fabricated/unlisted instance-lineage site rejects at
`buildCheckedSourceArchitecture`, before any sealed production result
can exist. The source-owned constructor cannot be used by external Haskell
callers. Strict Haskell and existing proof CI are required for actual
evidence credit; this document is not test evidence.

**Still open:** P6 stage handoffs must retain the identical producer event
through subject, branch/boundary and next-stage into the **whole selected
StageClosure**. P7 must make the same-event token a mandatory final
source/manifest/release accepting gate, with honest newly built
Upload/Steve positives and wrong-K (including same-I), swapped manifest,
stage/release/LLVM/trust, and forged/missing-token negatives. Existing
structural `certifyApplicationArtifact` / `certifyReleaseArtifact`
and NR-D06 generic source→unrelated stage fixtures remain weaker data
checks and are NOT producer-origin certification. No stage/release
provenance, Rocq native representation theorem, `FinalArtifactCertified`,
Phase 1 TCB change, normative case change or independent freeze is claimed.
Other P8–P11 obligations remain open. Independent Phase 1 freeze: NOT YET.
