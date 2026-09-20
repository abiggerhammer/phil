# PHIL-P1-REVIEW-R13 proof boundary

This slice certifies Astra Review R13: each **represented** provider-call site must agree with an independently supplied semantic expectation for both the exact provider occurrence and the exact qualified provider operation.

R13 composes with the already-Certified `PHIL-SYS-SUBJECT-AUTH-001` / SYS-005 provider-call boundary. The underlying provider stage must already have:

- an exact qualified provider binding rather than runtime-symbol coincidence;
- an accepted provider admission;
- exact required interface identity;
- a selected qualified provider operation;
- the exact implementation entry for that operation; and
- an internally exact represented call-site/link domain.

R13 then adds a separate expectation authority. `verifyProviderCallStageBundleAgainst` first runs the ordinary SYS-005 verifier, then for every represented link:

- requires an expectation for that call site;
- requires the expected provider occurrence to equal the occurrence in the exact provider binding; and
- requires the expected qualified operation to equal the operation in that binding.

This prevents a candidate link from defining its own semantic meaning. Borrowing a valid operation from a different provider rejects. Borrowing a different valid operation from the same provider also rejects.

Runtime symbol spelling is deliberately **not** part of the R13 semantic expectation. Changing only `providerCallRuntimeSymbol` leaves the exact occurrence/admission/interface/operation/entry binding unchanged and therefore remains nonauthoritative. A runtime-symbol-only provider binding is still rejected by the underlying SYS-005 verifier before the R13 expectation layer can accept it.

R13 is intentionally not a completeness theorem. `verifyProviderCallStageBundleAgainst` checks the semantic identity of every represented call, while **REVIEW-R14** separately requires equality between the independent required-site inventory and the candidate call-site domain.

The permanent four-case R13 regression uses Steve's provider-call stage to check exact acceptance, cross-provider donor rejection, same-provider/wrong-operation donor rejection, and runtime-symbol rename invariance. The dedicated gate also replays the existing SYS-005 provider correspondence and SYS-006 authority/effect controls.

Concrete `Map` traversal, `Text` and key equality, expectation provenance, provider-witness construction, runtime ABI/symbol realization, Haskell data representation, GHC/runtime correctness, and Rocq/toolchain correctness remain explicit implementation boundaries.
