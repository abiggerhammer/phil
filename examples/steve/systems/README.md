# Steve systems-pressure-test material

`lowering-contract.md` is the current Steve 0 mapping from the semantic/assurance witness into Phil's ADR-007/011 systems IR.

The contract is intentionally design-first rather than an executable `SystemsArtifact`. It identifies four systems-IR/verifier generalizations that must be expressible without semantic distortion before Steve should gain a branch-local systems fixture: first-class assumption-bound stage facts, multi-claim physical runtime sites, checked provider authority/call surfaces, and stable assurance-subject binding to owner/storage identity.

The current upload-derived systems implementation and proof corpus should be treated as the substrate to generalize, not copied around these gaps. Once those representation points are available, the promotion target is an executable Steve systems artifact plus adversarial mutations as listed in `lowering-contract.md`.

Main's PR #29 proof slice is now synchronized onto this branch as well. `PHIL-SYS-ID-001` proves the current systems artifact/lowering identity chain, and `PHIL-SYS-FACT-001` proves the current normalized stage-fact disposition rules. That strengthens the boundary Steve is pressure-testing: the four findings above are requests to generalize an already-mechanized representation, not uncertainty about what the current verifier means.
