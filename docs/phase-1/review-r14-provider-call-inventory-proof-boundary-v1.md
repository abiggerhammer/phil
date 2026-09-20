# PHIL-P1-REVIEW-R14 proof boundary

This slice certifies Astra Review R14: the independently supplied required provider-call inventory must be exactly equal to the candidate stage's represented provider-call site domain.

R14 is deliberately separate from R13.

- **R13** establishes the semantic identity of every represented call: exact provider occurrence plus exact qualified operation.
- **R14** establishes that the represented-call domain itself is complete relative to an independent required inventory.

That distinction closes a coordinated-deletion gap. The relative SYS-005 provider validator can remain internally consistent if a call site and its link are deleted together. Likewise, the relative SYS-006 authority/effect validator can remain internally consistent if the same call site, link, and use are deleted together. Neither relative check independently proves that a required call vanished.

The production completeness gate is `verifyProviderCallStageBundleCompleteAgainst`. It first runs the R13 correspondence gate, then requires:

`Map.keysSet expectations == providerCallStageCallSites bundle`.

Therefore:

- every independently required site must be represented;
- no unexpected represented site may exist;
- an empty relative candidate cannot count as complete when the independent inventory is nonempty; and
- coordinated site/link deletion is rejected even if the remaining provider stage is structurally valid.

`verifyAuthorityEffectStageBundleAgainst` propagates the same completeness authority through SYS-006 by invoking `verifyProviderCallStageBundleCompleteAgainst` on its provider-call base before running the ordinary authority/effect verification. A coordinated site/link/use deletion therefore cannot be hidden by the authority/effect layer.

The permanent six-case R14 regression checks exact Steve acceptance, relative-provider coordinated deletion acceptance, independent-provider deletion rejection, relative authority/effect coordinated deletion acceptance, independent authority/effect deletion rejection, and the empty-relative-inventory control. The dedicated proof gate also reruns R13 plus the existing SYS-005 and SYS-006 correspondence corpora.

Concrete `Map.keysSet`/`Set` equality, provenance and completeness of the expectation map itself, stage/witness construction, Haskell map/set representation, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
